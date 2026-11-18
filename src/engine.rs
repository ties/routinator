//! Updating and processing of RPKI data.
//!
//! This module provides types and traits implementing validation of RPKI data
//! from a set of trust anchor locators to some output data.
//!
//! Data validation is configured through [`Engine`] so that the
//! configuration can be used for multiple validation runs. This includes both
//! a [collector][crate::collector::Collector] and
//! [store][crate::store::Store] to use for validation.
//!
//! Individual validation runs are managed through [`Run`]. Such a runner can
//! be obtained from validation via its [`start`][Engine::start] method.
//! It in turn provides the [`process`][Run::process] method which drives the
//! actual validation.
//!
//! Engine runs are generic over what exactly should be done with valid
//! RPKI data. The trait [`ProcessRun`] represents a full validation run with
//! the accompanying trait [`ProcessPubPoint`] dealing with individual
//! publication points.

use std::{cmp, fmt, fs, thread};
use std::borrow::Cow;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fs::File;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};
use bytes::Bytes;
use crossbeam_queue::{ArrayQueue, SegQueue};
use log::{debug, error, info, warn};
use rand::seq::SliceRandom;
use rpki::crypto::keys::KeyIdentifier;
#[allow(unused_imports)]
use rpki::repository::aspa::{Aspa, AsProviderAttestation};
use rpki::repository::cert::{Cert, KeyUsage, ResourceCert};
use rpki::repository::crl::Crl;
use rpki::repository::error::{InspectionError, ValidationError};
use rpki::repository::manifest::{Manifest, ManifestContent, ManifestHash};
use rpki::repository::roa::{Roa, RouteOriginAttestation};
use rpki::repository::sigobj::SignedObject;
use rpki::repository::tal::{Tal, TalUri};
use rpki::repository::x509::{Time, Validity};
use rpki::uri;
use crate::{collector, store, tals};
use crate::config::{Config, FilterPolicy};
use crate::collector::Collector;
use crate::error::{Failed, Fatal, PubPointFailed, RunFailed};
use crate::log::{LogBook, LogBookWriter, Logger};
use crate::metrics::{
    Metrics, PublicationMetrics, RepositoryMetrics, TalMetrics
};
use crate::store::{
    Store, StoredManifest, StoredObject, StoredPoint, StoredStatus
};
use crate::utils::str::str_from_ascii;


//------------ Engine --------------------------------------------------------

/// The mechanism to update and process RPKI data.
///
/// A validation value can be created from the configuration via
/// [`Engine::new`]. If you don’t actually want to perform a validation run
/// but just initialize everything, [`Engine::init`] will suffice.
///
/// When created, the set of TALs is loaded and kept around. It will only be
/// refreshed explicitly through the [`reload_tals`][Self::reload_tals]
/// method.
///
/// Before starting the very first validation run, you need to call
/// [`ignite`][Self::ignite] at least once. As this may spawn threads, this
/// must happen after a possible fork.
///
/// A run is started via the [`start`][Self::start] method, providing a
/// processor that handles valid data. The method returns a [Run] value that
/// drives the validation run.
#[derive(Debug)]
pub struct Engine {
    /// A list of built-in TALs to use.
    bundled_tals: Vec<Tal>,

    /// An optional directory to load TALs from.
    extra_tals_dir: Option<PathBuf>,

    /// A mapping of TAL file names to TAL labels.
    tal_labels: HashMap<String, String>,

    /// The list of our TALs. 
    tals: Vec<Tal>,

    /// The collector to load updated data from.
    ///
    /// If this is `None`, updates have been disabled.
    collector: Option<Collector>,

    /// The store to load stored data from.
    store: Store,

    /// Should we be strict when decoding data?
    strict: bool,

    /// How do we deal with stale objects?
    stale: FilterPolicy,

    /// Number of validation threads.
    validation_threads: NonZeroUsize,

    /// Should we leave the repository dirty after a valiation run.
    dirty_repository: bool,

    /// Maximum depth of the CA chain.
    max_ca_depth: usize,

    /// The logger to use for repository issues (if any)
    repository_logger: Option<Arc<Logger>>,

    /// The maximum level we want to log repository messages for
    max_repository_level: log::LevelFilter,
}

impl Engine {
    /// Initializes the engine without creating a value.
    ///
    /// This ensures that the TAL directory is present and logs a hint how
    /// to achieve that if not.
    ///
    /// The function is called implicitly by [`new`][Self::new].
    pub fn init(config: &Config) -> Result<(), Failed> {
        Collector::init(config)?;
        Store::init(config)?;
        Ok(())
    }

    /// Creates a new engine.
    ///
    /// Takes all necessary information from `config`.
    /// It also takes over the provided cache and store for use during
    /// validation.
    ///
    /// Loads the initial set of TALs and errors out if that fails.
    pub fn new(
        config: &Config,
        update: bool,
    ) -> Result<Self, Failed> {
        let repository_logger =
            config.repository_log_target.as_ref().map(|target| {
                Logger::new(
                    target.clone(),
                    config.repository_log_level,
                    false, None,
                ).map(Arc::new)
            }).transpose()?;
        let collector = if update {
            Some(Collector::new(config, repository_logger.as_ref())?)
        }
        else {
            None
        };
        let store = Store::new(config)?;
        let mut res = Engine {
            bundled_tals: tals::collect_tals(config)?,
            extra_tals_dir: config.extra_tals_dir.clone(),
            tal_labels: config.tal_labels.clone(),
            tals: Vec::new(),
            collector,
            store,
            strict: config.strict,
            stale: config.stale,
            validation_threads: config.validation_threads,
            dirty_repository: config.dirty_repository,
            max_ca_depth: config.max_ca_depth,
            repository_logger,
            max_repository_level: config.repository_log_level,
        };
        res.reload_tals()?;
        Ok(res)
    }

    /// Disables the use of the collector, if previously enabled.
    ///
    /// Should be called before [`ignite`][Self::ignite].
    pub fn disable_collector(&mut self) {
        self.collector = None;
    }

    /// Returns the store status of the last run.
    pub fn store_status(&self) -> Result<Option<StoredStatus>, Failed> {
        self.store.status()
    }

    /// Reloads the set of TALs.
    ///
    /// Assumes that all regular files with an extension of `tal` in the
    /// TAL directory specified during object creation are TAL files and
    /// tries to load and decode them. Fails if that fails for at least one
    /// of those files.
    ///
    /// It is not considered an error if there are no TAL files in the TAL
    /// directory. However, a warning will be logged in this case.
    ///
    /// If there is more than one TAL for the same key, only the first of
    /// them by name is used. A warning is logged for each of the others.
    pub fn reload_tals(&mut self) -> Result<(), Failed> {
        let mut res = self.bundled_tals.clone();
        if let Some(extra_tals_dir) = self.extra_tals_dir.as_ref() {
            let dir = match fs::read_dir(extra_tals_dir) {
                Ok(dir) => dir,
                Err(err) => {
                    error!("Failed to open TAL directory {}: {}.",
                        extra_tals_dir.display(), err
                    );
                    return Err(Failed)
                }
            };
            for entry in dir {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(err) => {
                        error!(
                            "Failed to iterate over tal directory: {err}"
                        );
                        return Err(Failed)
                    }
                };

                if !entry.file_type().map(|ft| ft.is_file()).unwrap_or(false) {
                    continue
                }

                let path = entry.path();
                if path.extension().map(|ext| ext != "tal").unwrap_or(true) {
                    continue
                }

                let mut file = match File::open(&path) {
                    Ok(file) => {
                        file
                    }
                    Err(err) => {
                        error!(
                            "Failed to open TAL {}: {}. \n\
                             Aborting.",
                             path.display(), err
                        );
                        return Err(Failed)
                    }
                };
                let mut tal = match Tal::read_named(
                    self.path_to_tal_label(&path),
                    &mut file
                ) {
                    Ok(tal) => tal,
                    Err(err) => {
                        error!(
                            "Failed to read TAL {}: {}. \n\
                             Aborting.",
                            path.display(), err
                        );
                        return Err(Failed)
                    }
                };
                tal.prefer_https();
                res.push(tal);
            }
        }
        if res.is_empty() {
            warn!(
                "No TALs provided. Starting anyway."
            );
        }
        res.sort_by(|left, right| {
            left.info().name().cmp(right.info().name())
        });

        // The trust anchor certificate is selected and stored per key, so
        // there can only be one TAL for each key.
        let mut keys = HashMap::new();
        res.retain(|tal| {
            match keys.entry(tal.key_info().key_identifier()) {
                Entry::Occupied(first) => {
                    warn!(
                        "Skipping TAL {}: it has the same key as TAL {}.",
                        tal.info().name(), first.get()
                    );
                    false
                }
                Entry::Vacant(entry) => {
                    entry.insert(tal.info().name().to_string());
                    true
                }
            }
        });
        self.tals = res;

        Ok(())
    }

    /// Converts a path into a TAL label.
    ///
    /// This will be an explicitly configured TAL label if the file name
    /// portion of the path is registered in `self.tal_labels` or the file
    /// name without the `tal` extension otherwise.
    fn path_to_tal_label(&self, path: &Path) -> String {
        if let Some(name) = path.file_name().unwrap().to_str() {
            if let Some(label) = self.tal_labels.get(name) {
                return label.clone()
            }
        }
        path.file_stem().unwrap().to_string_lossy().into_owned()
    }

    /// Ignites validation processing.
    ///
    /// This spawns threads and therefore needs to be done after a
    /// possible fork.
    pub fn ignite(&mut self) -> Result<(), Failed> {
        if let Some(collector) = self.collector.as_mut() {
            collector.ignite()?;
        }
        Ok(())
    }

    /// Sanitizes the stored data.
    ///
    /// This goes over the stored data and deletes what looks broken. It
    /// should be called before retrying a failed restartable run.
    pub fn sanitize(&self) -> Result<(), Fatal> {
        self.store.sanitize()?;
        if let Some(collector) = self.collector.as_ref() {
            collector.sanitize()?;
        }
        Ok(())
    }

    /// Starts a validation run.
    ///
    /// During the run, `processor` will be responsible for dealing with
    /// valid objects. It must implement the [`ProcessRun`] trait.
    ///
    /// If `initial` is set to `true`, this will be an initial run which
    /// will operate without the collectors and return a non-fatal failure
    /// if any required publication points have not been referenced in the
    /// store, indicating that likely the configuration has changed and a
    /// full run is necessary.
    ///
    /// The method returns a [`Run`] that drives the validation run.
    pub fn start<P: ProcessRun>(
        &self, processor: P, initial: bool,
    ) -> Result<Run<'_, P>, Failed> {
        info!("Using the following TALs:");
        for tal in &self.tals {
            info!("  * {}", tal.info().name());
        }
        Ok(Run::new(
            self,
            if initial {
                None
            }
            else {
                self.collector.as_ref().map(Collector::start)
            },
            self.store.start(),
            processor,
            initial,
        ))
    }

    /// Dumps the content of the collector and store owned by the engine.
    pub fn dump(&self, dir: &Path) -> Result<(), Failed> {
        self.store.dump(dir)?;
        if let Some(collector) = self.collector.as_ref() {
            collector.dump(dir)?;
        }
        Ok(())
    }
}


//------------ Run -----------------------------------------------------------

/// A single validation run.
///
/// The runner is generic over the processor of valid data which must
/// implement the [`ProcessRun`] trait. The actual run is triggered by the
/// [`process`][Self::process] method. Upon completion, metrics of the run
/// can be extracted through [`done`][Self::done].
pub struct Run<'a, P> {
    /// A reference to the underlying validation.
    validation: &'a Engine,

    /// The runner for the collector.
    collector: Option<collector::Run<'a>>,

    /// The runner for the store.
    store: store::Run<'a>,

    /// The processor for valid data.
    processor: P,

    /// Is this an inital run?
    ///
    /// If `true`, a missing stored point will lead to a non-fatal error.
    initial: bool,

    /// Was an error encountered during the run?
    had_err: AtomicBool,

    /// Was a fatal error encountered during the run?
    is_fatal: AtomicBool,

    /// The metrics collected during the run.
    metrics: Metrics,
}

impl<'a, P> Run<'a, P> {
    /// Creates a new runner from all the parts.
    fn new(
        validation: &'a Engine,
        collector: Option<collector::Run<'a>>,
        store: store::Run<'a>,
        processor: P,
        initial: bool
    ) -> Self {
        Run {
            validation, collector, store, processor, initial,
            had_err: AtomicBool::new(false),
            is_fatal: AtomicBool::new(false),
            metrics: Default::default()
        }
    }

    /// Cleans the collector and store owned by the engine.
    pub fn cleanup(&mut self) -> Result<(), Failed> {
        if self.validation.dirty_repository {
            debug!("Skipping cleanup as configured.");
            return Ok(())
        }

        let mut retain = collector::Cleanup::new();
        self.store.cleanup(&mut retain)?;
        if let Some(collector) = self.collector.as_mut() {
            collector.cleanup(&mut retain)?;
        }
        Ok(())
    }

    /// Finishes the validation run and returns the metrics.
    ///
    /// If you are not interested in the metrics, you can simple drop the
    /// value, instead.
    pub fn done(self) -> Metrics {
        let mut metrics = self.metrics;
        if let Some(collector) = self.collector {
            collector.done(&mut metrics)
        }
        self.store.done(&mut metrics);
        metrics
    }
}

impl<P: ProcessRun> Run<'_, P> {
    /// Performs the validation run.
    pub fn process(&mut self) -> Result<(), RunFailed> {
        // If we don’t have any TALs, we ain’t got nothing to do.
        if self.validation.tals.is_empty() {
            return Ok(())
        }

        // Initialize our task queue with all the TALs.
        let metrics = RunMetrics::default();
        let tasks = SegQueue::new();
        for (index, tal) in self.validation.tals.iter().enumerate() {
            tasks.push(Task::Tal(TalTask { tal, index }));
            self.metrics.tals.push(TalMetrics::new(tal.info().clone()));
        }

        // And off we trot.

        // Keep a flag to cancel everything if something goes wrong.
        let thread_metrics = ArrayQueue::new(
            self.validation.validation_threads.get()
        );
        thread::scope(|scope| {
            for _ in 0 .. self.validation.validation_threads.get() {
                scope.spawn(|| {
                    let mut metrics = metrics.fork();
                    while let Some(task) = tasks.pop() {
                        if self.process_task(
                            task, &tasks, &mut metrics,
                        ).is_err() {
                            break;
                        }
                    }
                    thread_metrics.push(metrics).unwrap();
                });
            }
        });

        if self.had_err.load(Ordering::Relaxed) {
            if self.is_fatal.load(Ordering::Relaxed) {
                return Err(RunFailed::fatal())
            }
            else {
                return Err(RunFailed::retry())
            }
        }

        metrics.prepare_final(&mut self.metrics);
        while let Some(metrics) = thread_metrics.pop() {
            metrics.collapse(&mut self.metrics);
        }

        Ok(())
    }

    /// Process a task. Any task.
    fn process_task(
        &self,
        task: Task<P::PubPoint>,
        tasks: &SegQueue<Task<P::PubPoint>>,
        metrics: &mut RunMetrics,
    ) -> Result<(), Failed> {
        match task {
            Task::Tal(task) => {
                self.process_tal_task(task, tasks, metrics)
            }
            Task::Ca(task) => {
                self.process_ca_task(task, tasks, metrics)
            }
        }
    }

    /// Processes a trust anchor.
    fn process_tal_task(
        &self, task: TalTask,
        tasks: &SegQueue<Task<P::PubPoint>>,
        metrics: &mut RunMetrics,
    ) -> Result<(), Failed> {
        let fetched = self.fetch_ta(&task);

        // Fetching can take a while, so the time to check the cached
        // certificate against is only taken now.
        //
        // If this fails, the store is broken. We need to fail the whole run
        // and not just end this thread.
        let cert = self.select_ta(
            &task, fetched, Time::now()
        ).inspect_err(|_| {
            self.run_failed(RunFailed::fatal());
        })?;

        let Some(cert) = cert else {
            if self.initial {
                info!(
                    "Initial quick validation failed: \
                     no trust anchor for TAL {}.",
                    task.tal.info().name()
                );
                self.run_failed(RunFailed::retry());
                return Err(Failed)
            }
            else {
                warn!(
                    "No valid trust anchor for TAL {}",
                    task.tal.info().name()
                );
                return Ok(())
            }
        };

        debug!("Found valid trust anchor {}. Processing.", cert.uri());

        let processor = self.processor.process_ta(
            task.tal, cert.uri(), &cert, cert.tal
        ).inspect_err(|_| {
            self.run_failed(RunFailed::fatal());
        })?;
        match processor {
            Some(processor) => {
                self.process_ca_task(
                    CaTask {
                        cert, processor,
                        repository_index: None,
                        defer: false,
                    },
                    tasks, metrics,
                )
            }
            None => {
                debug!("Skipping trust anchor {}.", cert.uri());
                Ok(())
            }
        }
    }

    /// Processes a CA.
    fn process_ca_task(
        &self,
        task: CaTask<P::PubPoint>,
        tasks: &SegQueue<Task<P::PubPoint>>,
        metrics: &mut RunMetrics,
    ) -> Result<(), Failed> {
        let more_tasks = PubPoint::new(
            self, &task.cert, task.processor, task.repository_index,
        ).and_then(|point| {
            point.process(metrics)
        }).map_err(|err| {
            self.run_failed(err);
            Failed
        })?;
        for task in more_tasks {
            if self.had_err.load(Ordering::Relaxed) {
                return Err(Failed)
            }
            if task.defer {
                tasks.push(Task::Ca(task))
            }
            else {
                self.process_ca_task(task, tasks, metrics)?;
            }
        }
        Ok(())
    }

    /// Marks the run as failed.
    fn run_failed(&self, err: RunFailed) {
        self.had_err.store(true, Ordering::Relaxed);
        if err.is_fatal() {
            self.is_fatal.store(true, Ordering::Relaxed);
        }
    }
}

/// # Trust anchor certificate selection
///
/// The trust anchor certificate for a TAL is selected as described in
/// [RFC 10097]: The certificate retrieved during the run competes with the
/// certificate kept in the store from earlier runs. The one issued later
/// wins. If both were issued at the same time, the one that expires earlier
/// wins. This way, an old certificate cannot replace a newer one that has
/// been seen already.
///
/// [RFC 10097]: https://www.rfc-editor.org/rfc/rfc10097.html
impl<P> Run<'_, P> {
    /// Retrieves the trust anchor certificate for a TAL.
    ///
    /// Tries the URIs of the TAL in turn. Returns the first certificate that
    /// is a valid trust anchor certificate for the TAL at the time it was
    /// retrieved. Returns `None` if there isn’t one or if the run doesn’t
    /// have a collector.
    //
    //  Note that the rsync collector returns whatever is in its working copy
    //  even if updating the module has failed. This is fine since such a
    //  certificate still has to hold up against the stored certificate.
    fn fetch_ta(&self, task: &TalTask) -> Option<Arc<CaCert>> {
        let collector = self.collector.as_ref()?;
        for uri in task.tal.uris() {
            let Some(bytes) = collector.load_ta(uri) else {
                debug!("Trust anchor {uri}: no certificate retrieved.");
                continue
            };

            // Retrieving can take a while, so the time to check the
            // certificate against is only taken now.
            match self.check_ta(bytes, task, uri, Time::now()) {
                Ok(cert) => return Some(cert),
                Err(err) => warn!("Trust anchor {uri}: {err}."),
            }
        }
        None
    }

    /// Checks a candidate for the trust anchor certificate of a TAL.
    ///
    /// Returns the CA certificate to start validation from if `bytes`
    /// contains a valid trust anchor certificate for the TAL at `now`. The
    /// CA certificate will have the given URI.
    fn check_ta(
        &self, bytes: Bytes, task: &TalTask, uri: &TalUri, now: Time,
    ) -> Result<Arc<CaCert>, TaCertError> {
        let cert = check_ta_cert(
            bytes, task.tal, self.validation.strict, now
        )?;
        CaCert::root(
            cert, uri.clone(), task.index
        ).map_err(|_| TaCertError::NoCa)
    }

    /// Returns the cached trust anchor certificate for a TAL.
    ///
    /// This is the certificate stored for the key of the TAL. Only if
    /// nothing has been stored for the key yet, the certificates an earlier
    /// version of Routinator has left behind for the URIs of the TAL are
    /// looked at and the most preferred one of them is returned.
    ///
    /// The certificate has to be a valid trust anchor certificate for the
    /// TAL at `now`. Anything else is treated as if there was no cached
    /// certificate. The returned certificate will have the first URI of the
    /// TAL.
    //
    //  A cached certificate may not be valid yet if the clock was set back.
    //  It will be replaced by whatever is retrieved.
    //
    //  Once something was stored for the key, the certificates of earlier
    //  versions must not be looked at again, even if what was stored is not
    //  valid any more. They stay around until cleanup removes them and would
    //  otherwise replace a newer certificate after it has expired.
    fn cached_ta(
        &self, task: &TalTask, now: Time,
    ) -> Result<Option<Arc<CaCert>>, Failed> {
        // No URIs, no trust anchor.
        let Some(first_uri) = task.tal.uris().next() else {
            return Ok(None)
        };
        let check = |bytes| {
            self.check_ta(bytes, task, first_uri, now).inspect_err(|err| {
                info!(
                    "Cached trust anchor certificate for TAL {}: {err}. \
                     Ignoring.",
                    task.tal.info().name()
                );
            }).ok()
        };

        let key = task.tal.key_info().key_identifier();
        if let Some(bytes) = self.store.load_ta(key)? {
            return Ok(check(bytes))
        }

        let mut res: Option<Arc<CaCert>> = None;
        for uri in task.tal.uris() {
            let Some(cert) = self.store.load_legacy_ta(uri).and_then(
                &check
            ) else {
                continue
            };
            let preferred = res.as_ref().is_none_or(|res| {
                ta_preferred(
                    cert.cert().validity(), res.cert().validity()
                ).is_some()
            });
            if preferred {
                res = Some(cert)
            }
        }
        Ok(res)
    }

    /// Selects the trust anchor certificate to use for a TAL.
    ///
    /// The certificate retrieved during this run is given in `fetched`, if
    /// there is one. It is selected unless the cached certificate, which
    /// has to be valid at `now`, is preferred over it.
    ///
    /// If the run has a collector, the selected certificate is stored for
    /// use in later runs. A run without a collector doesn’t update anything
    /// and leaves the store alone.
    ///
    /// Returns `Ok(None)` if there is neither a retrieved nor a valid cached
    /// certificate.
    fn select_ta(
        &self, task: &TalTask, fetched: Option<Arc<CaCert>>, now: Time,
    ) -> Result<Option<Arc<CaCert>>, Failed> {
        let cert = match (fetched, self.cached_ta(task, now)?) {
            (Some(fetched), Some(cached)) => {
                let preferred = ta_preferred(
                    cached.cert().validity(), fetched.cert().validity()
                );
                match preferred {
                    // This is logged with every run until the cached
                    // certificate expires, so it isn’t a warning.
                    Some(reason) => {
                        info!(
                            "Trust anchor {}: retrieved certificate {} the \
                             cached certificate. Using the cached \
                             certificate.",
                            fetched.uri(),
                            match reason {
                                TaPreference::IssuedLater => "is older than",
                                TaPreference::ExpiresEarlier => {
                                    "has a longer validity than"
                                }
                            }
                        );
                        cached
                    }
                    // If neither is preferred, the retrieved certificate
                    // is used.
                    None => fetched,
                }
            }
            (Some(fetched), None) => fetched,
            (None, Some(cached)) => {
                if self.collector.is_some() {
                    info!(
                        "No trust anchor certificate retrieved for TAL {}. \
                         Using the cached certificate.",
                        task.tal.info().name()
                    );
                }
                cached
            }
            (None, None) => return Ok(None),
        };

        if self.collector.is_some() {
            self.store.update_ta(
                task.tal.key_info().key_identifier(),
                &cert.cert().to_captured()
            )?;
        }
        Ok(Some(cert))
    }
}


//------------ Trust Anchor Certificate Checks -------------------------------

/// The reason a trust anchor certificate is preferred over another one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TaPreference {
    /// The certificate has the more recent notBefore.
    IssuedLater,

    /// With the same notBefore, the certificate has the earlier notAfter.
    ExpiresEarlier,
}

/// Returns whether a trust anchor certificate is preferred over another one.
///
/// The certificates are for the same key and are given through their
/// validity. The function returns the reason if `left` is preferred over
/// `right`. It returns `None` if `right` is preferred or neither is.
///
/// This is the order defined by RFC 10097: The certificate with the more
/// recent notBefore is preferred. If notBefore is the same, the certificate
/// with the shorter validity, i.e., the earlier notAfter, is preferred.
//
//  This means that a certificate that was re-issued with nothing but a
//  later notAfter will not be used until the stored certificate has expired
//  or was removed.
fn ta_preferred(left: Validity, right: Validity) -> Option<TaPreference> {
    match left.not_before().cmp(&right.not_before()) {
        cmp::Ordering::Greater => Some(TaPreference::IssuedLater),
        cmp::Ordering::Less => None,
        cmp::Ordering::Equal => {
            (left.not_after() < right.not_after()).then_some(
                TaPreference::ExpiresEarlier
            )
        }
    }
}

/// Checks that `bytes` contains a valid trust anchor certificate for `tal`.
///
/// The certificate has to decode, has to have the key given in the TAL and
/// has to be a valid self-signed CA certificate at `now`.
fn check_ta_cert(
    bytes: Bytes, tal: &Tal, strict: bool, now: Time,
) -> Result<ResourceCert, TaCertError> {
    let cert = Cert::decode(bytes).map_err(|_| TaCertError::Decode)?;
    if cert.subject_public_key_info() != tal.key_info() {
        return Err(TaCertError::KeyMismatch)
    }
    cert.validate_ta_at(
        tal.info().clone(), strict, now
    ).map_err(TaCertError::Invalid)
}

/// The reason why a certificate can’t be the trust anchor for a TAL.
#[derive(Debug)]
enum TaCertError {
    /// The certificate failed to decode.
    Decode,

    /// The key of the certificate is not the key given in the TAL.
    KeyMismatch,

    /// The certificate is not a valid trust anchor certificate.
    Invalid(ValidationError),

    /// The certificate can’t be used as the certificate of a CA.
    //
    //  Validation checks for everything a CA certificate needs, so this
    //  should never happen.
    NoCa,
}

impl fmt::Display for TaCertError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TaCertError::Decode => f.write_str("failed to decode"),
            TaCertError::KeyMismatch => {
                f.write_str("key doesn’t match TAL")
            }
            TaCertError::Invalid(ref err) => err.fmt(f),
            TaCertError::NoCa => {
                f.write_str("not usable as a CA certificate")
            }
        }
    }
}


//------------ PubPoint ------------------------------------------------------

/// Validation of a single publication point.
struct PubPoint<'a, P: ProcessRun> {
    /// A reference to the runner.
    run: &'a Run<'a, P>,

    /// A reference to the CA certificate of the publication point.
    cert: &'a Arc<CaCert>,

    /// The processor for valid data at this publication point.
    processor: P::PubPoint,

    /// The index of this point’s repository in the run’s metrics.
    repository_index: Option<usize>,

    /// The base publication metrics for this publication point.
    ///
    /// This one only receives information about the publication point itself,
    /// as well as the manifest and manifest CRL. Everything else will be
    /// collected during object processing via `ValidPointManifest` so we can
    /// drop it if the point gets cancelled.
    metrics: PublicationMetrics,

    /// The log book writer for this publication point.
    log: LogBookWriter,
}

impl<'a, P: ProcessRun> PubPoint<'a, P> {
    /// Creates a new publication point validator based on a CA certificate.
    pub fn new(
        run: &'a Run<'a, P>,
        cert: &'a Arc<CaCert>,
        processor: P::PubPoint,
        repository_index: Option<usize>,
    ) -> Result<Self, RunFailed> {
        Ok(PubPoint {
            run, cert, processor, repository_index,
            metrics: Default::default(),
            log: LogBookWriter::new(
                run.validation.repository_logger.is_some().then(|| {
                    format!("{}: ", cert.ca_repository())
                }),
                run.validation.repository_logger.clone(),
                run.validation.max_repository_level,
            ),
        })
    }

    /// Performs validation of the publication point.
    ///
    /// Upon success, returns a list of all the child CAs of this publication
    /// point as CA processing tasks.
    pub fn process(
        self,
        metrics: &mut RunMetrics,
    ) -> Result<Vec<CaTask<P::PubPoint>>, RunFailed> {
        let mut store = match self.run.store.pub_point(self.cert) {
            Ok(store) => store,
            Err(PubPointFailed::Recoverable(kind)) => {
                warn!(
                    "{}: publication point could not be processed due to {}", 
                    self.cert.rpki_manifest(), kind
                );
                return Ok(Vec::new())
            },
            Err(PubPointFailed::Fatal) => return Err(RunFailed::fatal())
       };
        if self.run.initial && store.is_new() {
            info!(
                "Initial quick validation failed: \
                 encountered new publication point '{}'.",
                self.cert.rpki_manifest()
            );
            self.run.run_failed(RunFailed::retry());
            return Err(RunFailed::retry());
        }
        if let Some(collector) = self.run.collector.as_ref() {
            if let Some(collector) = collector.repository(self.cert)? {
                match self.process_collected(
                    collector, &mut store, metrics
                )? {
                    Ok(res) => return Ok(res),
                    Err(mut this) => {
                        this.metrics = Default::default();
                        return Ok(this.process_stored(store, metrics)?)
                    }
                }
            }
        }
        Ok(self.process_stored(store, metrics)?)
    }

    /// Tries to update the stored data and validate at the same time.
    ///
    /// Tries to fetch the updated manifest from the collector. If it differs
    /// from the stored manifest, updates the stored manifest and objects if
    /// the manifest is valid and all the objects are present and match their
    /// hashes. While checking, also processes the data so we only need to do
    /// that once.
    ///
    /// Returns a list of the child CAs if it successfully finished or `self`
    /// if there is no update or it is not valid and the store needs to be
    /// consulted.
    #[allow(clippy::type_complexity)] // Yeah, I know ...
    fn process_collected(
        mut self,
        collector: collector::Repository,
        store: &mut StoredPoint,
        metrics: &mut RunMetrics,
    ) -> Result<Result<Vec<CaTask<P::PubPoint>>, Self>, RunFailed> {
        // Try to load the manifest from the collector. If there isn’t one,
        // we are done.
        let collected = match collector.load_object(
            self.cert.rpki_manifest()
        )? {
            Some(collected) => collected,
            None => return Ok(Err(self))
        };

        // If the stored and collected manifests are the same, nothing has
        // changed and we can abort the update. However, we need to check that
        // the stored manifest refers to the same CA repository URI, just to
        // be sure.
        let same = if let Some(mft) = store.manifest() {
            mft.manifest == collected
                && mft.ca_repository == *self.cert.ca_repository()
        }
        else {
            false
        };
        if same {
            return Ok(Err(self))
        }

        // Validate the collected manifest. If it is no good, well, you know
        // the drill.
        let mut collected = match self.validate_collected_manifest(
            collected, &collector
        )? {
            Some(collected) => collected,
            None => {
                return Ok(Err(self))
            }
        };

        // Check that the collected manifest is newer. Otherwise return so
        // we use the stored manifest.
        if !self.check_collected_is_newer(&collected, store)? {
            return Ok(Err(self))
        }

        // The manifest is fine, so we can continue.
        //
        // First, report its validity to the processor.
        collected.point_validity(&mut self.processor);

        // Process detached objects first.
        self.processor.process_detached(
            self.cert, |cert| collected.check_crl(cert)
        )?;

        // We can look at the objects now. The objects are fine if they are
        // present and match the hash. If they don’t we have to cancel the
        // update. We also validate them while we are at it. This also
        // collects all the child CAs that need processing later on in
        // `ca_tasks`. 
        //
        // However, the processor can decide it doesn’t like the publication
        // point at all. This is not an error -- the publication point is
        // correct from a store perspective --, but we must not process the
        // collected `ca_tasks`. We keep track of this through `point_ok` and,
        // if that happens to end up being `false` return an empty list to
        // signal that the publication point was processed successfully but
        // shouldn’t be considered further.
        let mut ca_tasks = Vec::new();

        // Randomise the manifest to ensure a non-predictable ordering of the
        // child CAs. This is a preventative measure to stop CA children from
        // trying to influence the processing of the other children. It also
        // adds randomness to visiting the repositories, reducing peak load.
        let mut items_random: Vec<_> = collected.content.iter().collect();
        items_random.shuffle(&mut rand::rng());
        let mut items = items_random.into_iter();

        let mut point_ok = true;
        let update_result = store.update(
            &self.run.validation.store,
            StoredManifest::new(
                &collected.ee_cert,
                &collected.content,
                self.cert,
                collected.manifest_bytes.clone(),
                collected.crl_uri.clone(),
                collected.crl_bytes.clone(),
            ),
            || {
                let item = match items.next() {
                    Some(item) => item,
                    None => return Ok(None)
                };

                let file = match str_from_ascii(item.file()) {
                    Ok(file) => file,
                    Err(_) => {
                        self.log.error(format_args!(
                            "manifest {} contains illegal file name '{}'.",
                            self.cert.rpki_manifest(),
                            String::from_utf8_lossy(item.file())
                        ));
                        return Err(store::UpdateError::Abort)
                    }
                };
                let uri = self.cert.ca_repository().join(
                    file.as_ref()
                ).unwrap();

                let hash = ManifestHash::new(
                    item.hash().clone(), collected.content.file_hash_alg()
                );

                let content = match collector.load_object(&uri)? {
                    Some(content) => content,
                    None => {
                        self.log.error(format_args!(
                            "{uri}: failed to load."
                        ));
                        return Err(store::UpdateError::Abort)
                    }
                };

                if hash.verify(&content).is_err() {
                    self.log.error(format_args!(
                        "{uri}: file has wrong manifest hash."
                    ));
                    return Err(store::UpdateError::Abort)
                }

                if !self.process_object(
                    &uri, content.clone(),
                    &mut collected, &mut ca_tasks
                )? {
                    point_ok = false;
                }

                Ok(Some(StoredObject::new(uri, content, Some(hash))))
            }
        );

        match update_result {
            Ok(()) => {
                // Update was successful. We have to accept whatever result
                // we got.
                if point_ok {
                    self.accept_point(collected, metrics);
                    Ok(Ok(ca_tasks))
                }
                else {
                    self.reject_point(metrics);
                    Ok(Ok(Vec::new()))
                }
            }
            Err(store::UpdateError::Abort) => {
                // Update was aborted. We need to use the store.
                Ok(Err(self))
            }
            Err(store::UpdateError::Failed(err)) => {
                // We are doomed.
                Err(err)
            }
        }
    }

    /// Tries to validate a manifest acquired from the collector.
    ///
    /// Checks that the manifest is correct itself and has been signed by the
    /// publication point’s CA. Tries to load the associated CRL from the
    /// collector, validates that against the CA and checks that the manifest
    /// has not been revoked.
    fn validate_collected_manifest(
        &mut self,
        manifest_bytes: Bytes,
        repository: &collector::Repository,
    ) -> Result<Option<ValidPointManifest>, RunFailed> {
        let manifest = match Manifest::decode(
            manifest_bytes.clone(), self.run.validation.strict
        ) {
            Ok(manifest) => manifest,
            Err(_) => {
                self.metrics.invalid_manifests += 1;
                self.log.error(format_args!(
                    "failed to decode manifest {}.",
                    self.cert.rpki_manifest()
                ));
                return Ok(None)
            }
        };
        let (ee_cert, content) = match manifest.validate(
            self.cert.cert(), self.run.validation.strict
        ) {
            Ok(some) => some,
            Err(err) => {
                self.metrics.invalid_manifests += 1;
                self.log.warn(format_args!(
                    "manifest {}: {}.", self.cert.rpki_manifest(), err
                ));
                return Ok(None)
            }
        };

        if content.this_update() > Time::now() {
            self.metrics.premature_manifests += 1;
            self.log.warn(format_args!(
                "premature manifest {}", self.cert.rpki_manifest()
            ));
            return Ok(None)
        }

        if content.is_stale() {
            self.metrics.stale_manifests += 1;
            match self.run.validation.stale {
                FilterPolicy::Reject => {
                    self.log.warn(format_args!(
                        "rejecting stale manifest {}",
                        self.cert.rpki_manifest()
                    ));
                    return Ok(None)
                }
                FilterPolicy::Warn => {
                    self.log.warn(format_args!(
                        "stale manifest {}", self.cert.rpki_manifest()
                    ));
                }
                FilterPolicy::Accept => { }
            }
        }

        let (crl_uri, crl, crl_bytes) = match self.validate_collected_crl(
            &ee_cert, &content, repository
        )? {
            Some(some) => some,
            None => return Ok(None)
        };

        self.metrics.valid_manifests += 1;

        Ok(Some(ValidPointManifest {
            ee_cert, content, crl_uri, crl, manifest_bytes, crl_bytes,
            metrics: Default::default(),
        }))
    }

    /// Checks that the collected manifest is newer then a stored manifest.
    ///
    /// Checks that the collected manifest has a higher manifest number and
    /// a later thisUpdate date.
    ///
    /// The check is done against the “cached data” in the stored manifest.
    /// If the check fails, we also check if the cached data matches what’s
    /// in the actual stored manifest and, if that isn’t the case, discards
    /// the stored publication point.
    fn check_collected_is_newer(
        &mut self,
        collected: &ValidPointManifest,
        stored: &mut StoredPoint,
    ) -> Result<bool, Failed> {
        let Some(stored_mft) = stored.manifest() else {
            return Ok(true);
        };

        // Check if manifest number and this update are fine in which case we
        // can return already.
        if collected.content.manifest_number() > stored_mft.manifest_number
            && collected.content.this_update() > stored_mft.this_update
        {
            return Ok(true);
        }

        // Now parse the stored manifest and check that the numbers match.
        if let Ok(mft) = Manifest::decode(
            stored_mft.manifest.clone(), self.run.validation.strict
        ) {
            if mft.content().manifest_number() == stored_mft.manifest_number
                && mft.content().this_update() == stored_mft.this_update
            {
                // Same number, the stored manifest looks ok, so we can now
                // reject the collected. To print the right message, we have
                // to check again.

                if collected.content.manifest_number()
                    <= stored_mft.manifest_number
                {
                    self.log.warn(format_args!(
                        "manifest {}: manifest number is not greater than in \
                         stored version. Using stored publication point.",
                         self.cert.rpki_manifest(),
                    ));
                    return Ok(false);
                }
                if collected.content.this_update()
                    <= stored_mft.this_update
                {
                    self.log.warn(format_args!(
                        "manifest {}: manifest thisUpdate is not later than in \
                         stored version. Using stored publication point.",
                         self.cert.rpki_manifest(),
                    ));
                    return Ok(false);
                }
            }
        }

        // The stored manifest is broken. Remove it and then claim the
        // collected one is fine.
        stored.reject()?;
        Ok(true)
    }

    /// Check the manifest CRL.
    ///
    /// Checks that there is exactly one CRL on the manifest, that it matches
    /// the CRL mentioned in the manifest’s EE certificate, that it matches
    /// its manifest hash, that it is a valid CRL for the CA, and that it does
    /// not revoke the manifest’s EE certificate.
    ///
    /// If all that is true, returns the decoded CRL.
    fn validate_collected_crl(
        &mut self,
        ee_cert: &ResourceCert,
        manifest: &ManifestContent,
        repository: &collector::Repository
    ) -> Result<Option<(uri::Rsync, Crl, Bytes)>, RunFailed> {
        // Let’s first get the manifest CRL’s name relative to repo_uri. If
        // it ain’t relative at all, this is already invalid.
        let crl_uri = match ee_cert.crl_uri() {
            // RFC 6481: MUST end in .crl.
            Some(some) if some.ends_with(".crl") => some.clone(),
            Some(some) => {
                self.metrics.invalid_manifests += 1;
                self.log.error(format_args!("invalid CRL URI {}", some));
                return Ok(None)
            }
            None => {
                self.metrics.invalid_manifests += 1;
                self.log.error(format_args!(
                    "missing CRL URI on manifest {}",
                    self.cert.rpki_manifest()
                ));
                return Ok(None)
            }
        };
        let crl_name = match crl_uri.relative_to(self.cert.ca_repository()) {
            Some(name) => name,
            None => {
                self.metrics.invalid_manifests += 1;
                self.log.error(format_args!(
                    "CRL URI {crl_uri} outside repository directory."
                ));
                return Ok(None)
            }
        };

        // Now we go over the manifest and try to find an entry matching
        // crl_name.
        let mut crl_bytes = None;
        for item in manifest.iter() {
            let (file, hash) = item.into_pair();
            if file == crl_name {
                let bytes = match repository.load_object(&crl_uri)? {
                    Some(bytes) => bytes,
                    None => {
                        self.metrics.invalid_crls += 1;
                        self.log.warn(format_args!(
                            "{crl_uri}: failed to load."
                        ));
                        return Ok(None)
                    }
                };
                let hash = ManifestHash::new(hash, manifest.file_hash_alg());
                if hash.verify(&bytes).is_err() {
                    self.metrics.invalid_crls += 1;
                    self.log.error(format_args!(
                        "file {crl_uri} has wrong hash."
                    ));
                    return Ok(None)
                }
                crl_bytes = Some(bytes);
            }
        }
        let crl_bytes = match crl_bytes {
            Some(some) => some,
            None => {
                self.metrics.invalid_crls += 1;
                self.log.error(format_args!("CRL not listed on manifest."));
                return Ok(None)
            }
        };

        // Decode and validate the CRL.
        let mut crl = match Crl::decode(crl_bytes.clone()) {
            Ok(crl) => crl,
            Err(_) => {
                self.metrics.invalid_crls += 1;
                self.log.error(format_args!(
                    "CRL {crl_uri}: failed to decode."
                ));
                return Ok(None)
            }
        };
        if let Err(err) = crl.verify_signature(
            self.cert.cert().subject_public_key_info()
        ) {
            self.metrics.invalid_crls += 1;
            self.log.warn(format_args!("CRL {crl_uri}: {err}."));
            return Ok(None)
        }
        if crl.this_update() > Time::now() {
            self.metrics.invalid_crls += 1;
            self.log.warn(format_args!("CRL {crl_uri}: not yet valid."));
            return Ok(None);
        }
        if crl.is_stale() {
            self.metrics.stale_crls += 1;
            match self.run.validation.stale {
                FilterPolicy::Reject => {
                    self.log.warn(format_args!(
                        "rejecting stale CRL {crl_uri}."
                    ));
                    return Ok(None)
                }
                FilterPolicy::Warn => {
                    self.log.warn(format_args!("stale CRL {crl_uri}."));
                }
                FilterPolicy::Accept => { }
            }
        }

        // Check that this CRL actually belongs to this CA
        if let Err(err) = crl.verify_issuer_claim(self.cert.cert(), false) {
            self.metrics.invalid_crls += 1;
            self.log.warn(format_args!("CRL {crl_uri}: {err}."));
            return Ok(None)
        }

        // Turn on serial caching before looking for the first serial.
        crl.cache_serials();

        // Finally: has the manifest’s cert been revoked?
        if crl.contains(ee_cert.serial_number()) {
            self.metrics.invalid_manifests += 1;
            self.log.warn(format_args!(
                "manifest certificate has been revoked."
            ));
            return Ok(None)
        }

        // Phew: All good.
        self.metrics.valid_crls += 1;
        Ok(Some((crl_uri, crl, crl_bytes)))
    }

    /// Process the stored version of the publication point.
    ///
    /// Validates the objects of the currently stored version of the
    /// publication point if there is one.
    ///
    /// Returns a list of all child CAs of this publication point.
    fn process_stored(
        mut self,
        mut store: StoredPoint,
        metrics: &mut RunMetrics,
    ) -> Result<Vec<CaTask<P::PubPoint>>, Failed> {
        let manifest = match store.manifest() {
            Some(manifest) => manifest,
            None => {
                // We don’t seem to have this point in the store either.
                // Warn and return.
                self.log.warn(format_args!(
                    "no valid manifest {} found.",
                    self.cert.rpki_manifest()
                ));
                self.metrics.missing_manifests += 1;
                self.reject_point(metrics);
                return Ok(Vec::new())
            }
        };

        let mut manifest = match self.validate_stored_manifest(manifest) {
            Ok(manifest) => manifest,
            Err(_) => {
                self.reject_point(metrics);
                return Ok(Vec::new())
            }
        };

        manifest.point_validity(&mut self.processor);

        self.processor.process_detached(
            self.cert, |cert| manifest.check_crl(cert)
        )?;

        let mut ca_tasks = Vec::new();
        for object in &mut store {
            let object = match object {
                Ok(object) => object,
                Err(err) => {
                    if err.is_fatal() {
                        error!(
                            "Fatal: failed to read from {}: {}",
                            store.path().display(), err
                        );
                        return Err(Failed)
                    }
                    else {
                        debug!(
                            "Ignoring invalid stored publication point \
                             at {}: {}",
                            store.path().display(), err
                        );
                        self.reject_point(metrics);
                        return Ok(Vec::new())
                    }
                }
            };
            if !self.process_object(
                &object.uri, object.content.clone(),
                &mut manifest, &mut ca_tasks
            )? {
                self.reject_point(metrics);
                return Ok(Vec::new())
            }
        }

        self.accept_point(manifest, metrics);
        Ok(ca_tasks)
    }

    /// Tries to validate a stored manifest.
    ///
    /// This is similar to
    /// [`validate_collected_manifest`][Self::validate_collected_manifest]
    /// but has less hassle with the CRL because that is actually included in
    /// the stored manifest.
    fn validate_stored_manifest(
        &mut self,
        stored_manifest: &StoredManifest,
    ) -> Result<ValidPointManifest, Failed> {
        // Decode and validate the manifest.
        let manifest = match Manifest::decode(
            stored_manifest.manifest.clone(), self.run.validation.strict
        ) {
            Ok(manifest) => manifest,
            Err(_) => {
                self.metrics.invalid_manifests += 1;
                self.log.error(format_args!(
                    "failed to decode manifest {}.",
                    self.cert.rpki_manifest(),
                ));
                return Err(Failed);
            }
        };
        let (ee_cert, content) = match manifest.validate(
            self.cert.cert(), self.run.validation.strict
        ) {
            Ok(some) => some,
            Err(err) => {
                self.log.warn(format_args!(
                    "manifest {}: {}.",
                    self.cert.rpki_manifest(), err
                ));
                self.metrics.invalid_manifests += 1;
                return Err(Failed);
            }
        };
        if content.is_stale() {
            self.metrics.stale_manifests += 1;
            match self.run.validation.stale {
                FilterPolicy::Reject => {
                    self.log.warn(format_args!(
                        "rejecting stale manifest {}",
                        self.cert.rpki_manifest()
                    ));
                    self.metrics.invalid_manifests += 1;
                    return Err(Failed);
                }
                FilterPolicy::Warn => {
                    self.log.warn(format_args!(
                        "stale manifest {}", self.cert.rpki_manifest()
                    ));
                }
                FilterPolicy::Accept => { }
            }
        }

        // Get the CRL URI. We actually only need this for error reporting.
        let crl_uri = match ee_cert.crl_uri() {
            Some(uri) => uri.clone(),
            None => {
                // This should have been ruled out in manifest validation.
                self.log.warn(format_args!("manifest without CRL URI."));
                self.metrics.invalid_manifests += 1;
                return Err(Failed)
            }
        };

        // Decode and validate the CRL.
        let mut crl = match Crl::decode(stored_manifest.crl.clone()) {
            Ok(crl) => crl,
            Err(_) => {
                self.metrics.invalid_manifests += 1;
                self.metrics.invalid_crls += 1;
                self.log.error(format_args!(
                    "failed to decode CRL {crl_uri}."
                ));
                return Err(Failed)
            }
        };
        if let Err(err) = crl.verify_signature(
            self.cert.cert().subject_public_key_info()
        ) {
            self.log.warn(format_args!("CRL {crl_uri}: {err}."));
            self.metrics.invalid_manifests += 1;
            self.metrics.invalid_crls += 1;
            return Err(Failed)
        }
        if crl.is_stale() {
            self.metrics.stale_crls += 1;
            match self.run.validation.stale {
                FilterPolicy::Reject => {
                    self.log.warn(format_args!(
                        "rejecting stale CRL {crl_uri}."
                    ));
                    self.metrics.invalid_manifests += 1;
                    self.metrics.invalid_crls += 1;
                    return Err(Failed)
                }
                FilterPolicy::Warn => {
                    self.log.warn(format_args!(
                        "stale CRL {crl_uri}."
                    ));
                }
                FilterPolicy::Accept => { }
            }
        }

        // Turn on serial caching before looking for the first serial.
        crl.cache_serials();

        // Finally: has the manifest’s cert been revoked?
        //
        // XXX This shouldn’t really happen because if it were we would never
        //     have stored this manifest.
        if crl.contains(ee_cert.serial_number()) {
            self.log.warn(format_args!(
                "manifest {}: certificate has been revoked.",
                self.cert.rpki_manifest()
            ));
            self.metrics.invalid_manifests += 1;
            return Err(Failed)
        }

        self.metrics.valid_manifests += 1;
        self.metrics.valid_crls += 1;
        Ok(ValidPointManifest {
            ee_cert, content, crl_uri, crl,
            manifest_bytes: stored_manifest.manifest.clone(),
            crl_bytes: stored_manifest.crl.clone(),
            metrics: Default::default(),
        })
    }

    // XXX Check metrics generation and concentrate at one central point.

    fn accept_point(
        mut self,
        manifest: ValidPointManifest,
        metrics: &mut RunMetrics,
    ) {
        self.metrics.valid_points += 1;
        self.metrics += manifest.metrics;
        self.apply_metrics(metrics);
        self.processor.commit();
    }

    fn reject_point(
        mut self,
        metrics: &mut RunMetrics,
    ) {
        self.metrics.rejected_points += 1;
        self.apply_metrics(metrics);
        self.processor.cancel(self.cert);
        let log = self.log.into_book();
        if !log.is_empty() {
            metrics.append_log(self.cert.ca_repository().clone(), log);
        }
    }

    fn apply_metrics(
        &mut self,
        metrics: &mut RunMetrics,
    ) {
        let repository_index = self.repository_index.unwrap_or_else(|| {
            metrics.repository_index(self.cert)
        });
        self.processor.repository_index(repository_index);
        metrics.apply(
            &self.metrics,
            repository_index,
            self.cert.tal,
        );
    }

    /// Processes a single object.
    ///
    /// Returns whether processing should continue or whether the entire (!)
    /// publication point should be disregarded.
    fn process_object(
        &mut self,
        uri: &uri::Rsync,
        content: Bytes,
        manifest: &mut ValidPointManifest,
        ca_task: &mut Vec<CaTask<P::PubPoint>>,
    ) -> Result<bool, Failed> {
        if !self.processor.want(uri)? {
            return Ok(true)
        }

        if uri.ends_with(".cer") {
            self.process_cer(uri, content, manifest, ca_task)?;
        }
        else if uri.ends_with(".roa") {
            self.process_roa(uri, content, manifest)?;
        }
        else if uri.ends_with(".asa") {
            self.process_aspa(uri, content, manifest)?;
        }
        else if uri.ends_with(".gbr") {
            self.process_gbr(uri, content, manifest)?;
        }
        else if uri.ends_with(".crl") {
            if *uri != manifest.crl_uri {
                self.log.warn(format_args!("stray CRL {uri}."));
                manifest.metrics.stray_crls += 1;
            }
        }
        else {
            manifest.metrics.others += 1;
            self.log.warn(format_args!(
                "object {uri}: unknown type."
            ));
        }
        Ok(true)
    }

    /// Processes a certificate object.
    fn process_cer(
        &mut self,
        uri: &uri::Rsync,
        content: Bytes,
        manifest: &mut ValidPointManifest,
        ca_task: &mut Vec<CaTask<P::PubPoint>>,
    ) -> Result<(), Failed> {
        let cert = match Cert::decode(content) {
            Ok(cert) => cert,
            Err(_) => {
                manifest.metrics.invalid_certs += 1;
                self.log.error(format_args!(
                    "certificate {uri}: failed to decode."
                ));
                return Ok(())
            }
        };

        if cert.key_usage() == KeyUsage::Ca {
            self.process_ca_cer(uri, cert, manifest, ca_task)
        }
        else {
            self.process_router_cert(uri, cert, manifest)
        }
    }

    /// Processes a CA certificate.
    #[allow(clippy::too_many_arguments)]
    fn process_ca_cer(
        &mut self, uri: &uri::Rsync, cert: Cert,
        manifest: &mut ValidPointManifest,
        ca_task: &mut Vec<CaTask<P::PubPoint>>,
    ) -> Result<(), Failed> {
        if self.cert.check_loop(&cert).is_err() {
            self.log.error(format_args!(
                "CA certificate {uri}: certificate loop detected."
            ));
            manifest.metrics.invalid_certs += 1;
            return Ok(())
        }
        let cert = match cert.validate_ca(
            self.cert.cert(), self.run.validation.strict
        ) {
            Ok(cert) => cert,
            Err(err) => {
                self.log.warn(format_args!(
                    "CA certificate {uri}: {err}."
                ));
                manifest.metrics.invalid_certs += 1;
                return Ok(())
            }
        };
        if let Err(err) = manifest.check_crl(&cert) {
            self.log.warn(format_args!(
                "CA certificate {uri}: {err}."
            ));
            manifest.metrics.invalid_certs += 1;
            return Ok(())
        }

        let cert = match CaCert::chain(
            self.cert, uri.clone(), cert, self.run.validation.max_ca_depth,
        ) {
            Ok(cert) => cert,
            Err(_) => {
                manifest.metrics.invalid_certs += 1;
                return Ok(())
            }
        };

        manifest.metrics.valid_ca_certs += 1;

        let processor = match self.processor.process_ca(
            uri, &cert
        )? {
            Some(processor) => processor,
            None => return Ok(())
        };

        // Defer operation if we need to update the repository part where
        // the CA lives.
        let defer = match self.run.collector.as_ref() {
            Some(collector) => !collector.was_updated(&cert),
            None => false,
        };

        // If we switch repositories, we need to apply our metrics.
        let repository_index = if cert.repository_switch() {
            None
        }
        else {
            self.repository_index
        };

        ca_task.push(CaTask {
            cert, processor, repository_index, defer
        });
        Ok(())
    }

    /// Processes a router certificate.
    fn process_router_cert(
        &mut self, uri: &uri::Rsync, cert: Cert,
        manifest: &mut ValidPointManifest,
    ) -> Result<(), Failed> {
        if let Err(err) = cert.validate_router(
            self.cert.cert(), self.run.validation.strict
        ) {
            self.log.warn(format_args!(
                "router certificate {uri}: {err}."
            ));
            manifest.metrics.invalid_certs += 1;
            return Ok(())
        };
        if let Err(err) = manifest.check_crl(&cert) {
            self.log.warn(format_args!(
                "router certificate {uri}: {err}."
            ));
            manifest.metrics.invalid_certs += 1;
            return Ok(())
        }
        manifest.metrics.valid_router_certs += 1;
        self.processor.process_router_cert(uri, cert, self.cert)?;
        Ok(())
    }

    /// Processes a ROA object.
    fn process_roa(
        &mut self, uri: &uri::Rsync, content: Bytes,
        manifest: &mut ValidPointManifest,
    ) -> Result<(), Failed> {
        let roa = match Roa::decode(
            content, self.run.validation.strict
        ) {
            Ok(roa) => roa,
            Err(_) => {
                manifest.metrics.invalid_roas += 1;
                self.log.error(format_args!(
                    "ROA {uri}: failed to decode."
                ));
                return Ok(())
            }
        };
        match roa.process(
            self.cert.cert(),
            self.run.validation.strict,
            |cert| manifest.check_crl(cert)
        ) {
            Ok((cert, route)) => {
                manifest.metrics.valid_roas += 1;
                self.processor.process_roa(uri, cert, route)?
            }
            Err(err) => {
                manifest.metrics.invalid_roas += 1;
                self.log.warn(format_args!(
                    "ROA {uri}: {err}."
                ))
            }
        }
        Ok(())
    }

    /// Process an ASPA object.
    #[allow(unused_variables)]
    fn process_aspa(
        &mut self, uri: &uri::Rsync, content: Bytes,
        manifest: &mut ValidPointManifest,
    ) -> Result<(), Failed> {
        let aspa = match Aspa::decode(
            content, self.run.validation.strict
        ) {
            Ok(aspa) => aspa,
            Err(err) => {
                manifest.metrics.invalid_aspas += 1;
                self.log.error(format_args!(
                    "ASPA {uri}: failed to decode."
                ));
                return Ok(())
            }
        };
        match aspa.process(
            self.cert.cert(),
            self.run.validation.strict,
            |cert| manifest.check_crl(cert)
        ) {
            Ok((cert, aspa)) => {
                manifest.metrics.valid_aspas += 1;
                self.processor.process_aspa(uri, cert, aspa)?
            }
            Err(err) => {
                manifest.metrics.invalid_aspas += 1;
                self.log.warn(format_args!(
                    "ASPA {uri}: {err}."
                ))
            }
        }
        Ok(())
    }

    /// Processes a Ghostbuster Record.
    fn process_gbr(
        &mut self, uri: &uri::Rsync, content: Bytes,
        manifest: &mut ValidPointManifest,
    ) -> Result<(), Failed> {
        let obj = match SignedObject::decode(
            content, self.run.validation.strict
        ) {
            Ok(obj) => obj,
            Err(_) => {
                manifest.metrics.invalid_gbrs += 1;
                self.log.error(format_args!(
                    "GBR {uri}: failed to decode."
                ));
                return Ok(())
            }
        };
        match obj.process(
            self.cert.cert(),
            self.run.validation.strict,
            |cert| manifest.check_crl(cert)
        ) {
            Ok((cert, content)) => {
                manifest.metrics.valid_gbrs += 1;
                self.processor.process_gbr(uri, cert, content)?
            }
            Err(err) => {
                manifest.metrics.invalid_gbrs += 1;
                self.log.warn(format_args!(
                    "GBR {uri}: {err}."
                ))
            }
        }
        Ok(())
    }
}


//------------ ValidPointManifest --------------------------------------------

/// All information from a validated manifest.
#[derive(Clone, Debug)]
struct ValidPointManifest {
    /// The EE certificate the manifest was signed with.
    ee_cert: ResourceCert,

    /// The payload of the manifest.
    content: ManifestContent,

    /// The CRL distribution point URI of the manifest.
    ///
    /// This is here separately because it may be `None` in a `ResourceCert`
    /// but can’t be in a valid CA cert.
    crl_uri: uri::Rsync,

    /// The CRL.
    crl: Crl,

    /// The raw bytes of the manifest.
    manifest_bytes: Bytes,

    /// The raw bytes of the CRL.
    crl_bytes: Bytes,

    /// The publication metrics collected while processing the manifest.
    ///
    /// We keep them here separatedly, so we can just zero them out if
    /// processor decides to drop the publication point.
    metrics: PublicationMetrics,
}

impl ValidPointManifest {
    /// Checks whether `cert` has been revoked.
    fn check_crl(&self, cert: &Cert) -> Result<(), ValidationError> {
        let crl_uri = match cert.crl_uri() {
            Some(some) => some,
            None => {
                return Err(InspectionError::new(
                    "certificate has no CRL URI"
                ).into())
            }
        };

        if *crl_uri != self.crl_uri {
            return Err(InspectionError::new(
                "certificate's CRL differs from manifest's"
            ).into())
        }

        if self.crl.contains(cert.serial_number()) {
            return Err(InspectionError::new(
                "certificate has been revoked"
            ).into())
        }

        Ok(())
    }

    /// Reports the validity to the given processor.
    fn point_validity(&self, processor: &mut impl ProcessPubPoint) {
        processor.point_validity(
            self.ee_cert.validity(),
            cmp::min(
                self.content.next_update(),
                self.crl.next_update(),
            )
        )
    }
}


//------------ Task ----------------------------------------------------------

/// Any task that can be queued for delayed processing.
enum Task<'a, P> {
    /// The task is to process a trust anchor locator.
    Tal(TalTask<'a>),

    /// The task is to process a CA.
    Ca(CaTask<P>),
}

impl<P> fmt::Debug for Task<'_, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Task::Tal(ref inner) => {
                write!(f, "TalTask {{ tal: {} }}", inner.tal.info().name())
            }
            Task::Ca(ref inner) => {
                write!(
                    f, "CaTask {{ ca_repository: {} }}",
                    inner.cert.ca_repository
                )
            }
        }
    }
}


//------------ TalTask ------------------------------------------------------

/// A task for processing a single trust anchor locator.
struct TalTask<'a> {
    /// A reference to the actual TAL.
    tal: &'a Tal,

    /// The index of this TAL in the metrics.
    index: usize,
}


//------------ CaTask --------------------------------------------------------

/// A task for processing a single CA.
struct CaTask<P> {
    /// The CA certificate of the CA.
    cert: Arc<CaCert>,

    /// The processor for this CA.
    processor: P,

    /// The repository index of we know it already.
    repository_index: Option<usize>,

    /// Defer processing?
    ///
    /// Processing is deferred if the CA lives in a different repository than
    /// its issuing CA:
    defer: bool,
}


//------------ CaCert --------------------------------------------------------

/// A CA certificate plus references to all its parents.
///
/// Note that this does not represent the full publication point, only the
/// certificate itself.
#[derive(Clone, Debug)]
pub struct CaCert {
    /// The CA certificate of this CA.
    cert: ResourceCert,

    /// The certificate’s location.
    ///
    /// Don’t be confused by the type – this is a TAL URI because it can be
    /// an HTTPS URI for TAL certificates. But it definitely isn’t the URI
    /// of the TAL this was derived from, it is the actual URI of the actual
    /// certificate.
    uri: TalUri,

    /// The CA repository URI of the certificate.
    ca_repository: uri::Rsync,

    /// The manifest URI of the certificate.
    rpki_manifest: uri::Rsync,

    /// The parent CA.
    /// 
    /// This will be `None` for a trust anchor certificate.
    parent: Option<Arc<CaCert>>,

    /// The length of the chain of certificates from a trust anchor.
    chain_len: usize,

    /// The index of the TAL in the metrics.
    pub(crate) // XXX
    tal: usize,
}

impl CaCert {
    /// Creates a new CA cert for a trust anchor.
    pub fn root(
        cert: ResourceCert, uri: TalUri, tal: usize
    ) -> Result<Arc<Self>, Failed> {
        Self::new(cert, uri, None, 0, tal)
    }

    /// Creates a new CA cert for an issued CA.
    pub fn chain(
        issuer: &Arc<Self>,
        uri: uri::Rsync,
        cert: ResourceCert,
        max_depth: usize,
    ) -> Result<Arc<Self>, Failed> {
        let chain_len = match issuer.chain_len.checked_add(1) {
            Some(chain_len) => chain_len,
            None => {
                error!(
                    "CA {uri}: CA depth overrun."
                );
                return Err(Failed)
            }
        };
        if chain_len > max_depth {
            error!(
                "CA {uri}: CA depth overrun."
            );
            return Err(Failed)
        }
        Self::new(
            cert, TalUri::Rsync(uri),
            Some(issuer.clone()), chain_len,
            issuer.tal
        )
    }

    /// Creates a new CA cert from its various parts.
    fn new(
        cert: ResourceCert,
        uri: TalUri, 
        parent: Option<Arc<Self>>,
        chain_len: usize,
        tal: usize,
    ) -> Result<Arc<Self>, Failed> {
        let ca_repository = match cert.ca_repository() {
            Some(uri) => uri.clone(),
            None => {
                // This is actually checked during certificate validation,
                // so this should never happen.
                error!(
                    "CA cert {uri} has no repository URI. \
                     Why has it not been rejected yet?"
                );
                return Err(Failed)
            }
        };
        
        let rpki_manifest = match cert.rpki_manifest() {
            Some(uri) => uri.clone(),
            None => {
                // This is actually checked during certificate validation,
                // so this should never happen.
                error!(
                    "CA cert {uri} has no manifest URI. \
                     Why has it not been rejected yet?"
                );
                return Err(Failed)
            }
        };
        Ok(Arc::new(CaCert {
            cert, uri, ca_repository, rpki_manifest, parent, chain_len, tal
        }))
    }

    /// Checks whether a child cert has appeared in the chain already.
    pub fn check_loop(&self, cert: &Cert) -> Result<(), Failed> {
        self._check_loop(cert.subject_key_identifier())
    }

    /// The actual recursive loop test.
    ///
    /// We are comparing certificates by comparing their subject key
    /// identifiers.
    fn _check_loop(&self, key_id: KeyIdentifier) -> Result<(), Failed> {
        if self.cert.subject_key_identifier() == key_id {
            Err(Failed)
        }
        else if let Some(ref parent) = self.parent {
            parent._check_loop(key_id)
        }
        else {
            Ok(())
        }
    }

    /// Returns a reference to the resource certificate.
    pub fn cert(&self) -> &ResourceCert {
        &self.cert
    }

    /// Returns a reference to the certificate’s URI.
    ///
    /// Note that this really is the URI of the certificate itself despite
    /// the type of `TalUri`. This type is used because TAL certificates
    /// (which are CA certificates) are published with an HTTPS URI rather
    /// than an rsync URI.
    pub fn uri(&self) -> &TalUri {
        &self.uri
    }

    /// Returns a reference the caRepository URI of the certificate.
    pub fn ca_repository(&self) -> &uri::Rsync {
        &self.ca_repository
    }

    /// Returns a reference to the rpkiManifest URI of the certificate.
    pub fn rpki_manifest(&self) -> &uri::Rsync {
        &self.rpki_manifest
    }

    /// Returns a reference to the rpkiNotify URI of the certificate.
    pub fn rpki_notify(&self) -> Option<&uri::Https> {
        self.cert.rpki_notify()
    }

    /// Returns whether the CA is in a different repository from its parent.
    ///
    /// This is just a quick check and may report a switch when in fact there
    /// isn’t one.
    pub(crate) // XXX
    fn repository_switch(&self) -> bool {
        let parent = match self.parent.as_ref() {
            Some(parent) => parent,
            None => return true,
        };

        match self.rpki_notify() {
            Some(rpki_notify) => {
                Some(rpki_notify) != parent.rpki_notify()
            }
            None => {
                self.ca_repository.module() != parent.ca_repository.module()
            }
        }
    }
} 


//------------ RunMetrics ----------------------------------------------------

/// The metrics collected during a engine run.
#[derive(Debug, Default)]
struct RunMetrics {
    /// The per-TAL metrics.
    tals: Vec<PublicationMetrics>,

    /// The per-repository metrics.
    repositories: Vec<PublicationMetrics>,

    /// The overall metrics.
    publication: PublicationMetrics,

    /// The log books for publication points with issues.
    log_books: Vec<(uri::Rsync, LogBook)>,

    /// The indexes of repositories in the repository metrics vec.
    ///
    /// The key is the string representation of the rpkiNotify or rsync
    /// module URI.
    repository_indexes: Arc<Mutex<HashMap<String, usize>>>,
}

impl RunMetrics {
    /// Creates a new value that shares indexes with the current one.
    pub fn fork(&self) -> Self {
        RunMetrics {
            tals: Default::default(),
            repositories: Default::default(),
            publication: Default::default(),
            repository_indexes: self.repository_indexes.clone(),
            log_books: Default::default(),
        }
    }

    /// Returns the index of a repository in the metrics.
    ///
    /// Adds a new repository if necessary.
    pub fn repository_index(&self, cert: &CaCert) -> usize {
        let uri = cert.rpki_notify().map(|uri| {
            Cow::Borrowed(uri.as_str())
        }).unwrap_or_else(|| {
            cert.ca_repository.canonical_module()
        });

        let mut repository_indexes = self.repository_indexes.lock().unwrap();
        if let Some(index) = repository_indexes.get(uri.as_ref()) {
            return *index
        }

        let index = repository_indexes.len();
        repository_indexes.insert(uri.into_owned(), index);
        index
    }

    /// Apply publication metrics.
    pub fn apply(
        &mut self, metrics: &PublicationMetrics,
        repository_index: usize, tal_index: usize,
    ) {
        while self.repositories.len() <= repository_index {
            self.repositories.push(Default::default())
        }
        self.repositories[repository_index] += metrics;

        while self.tals.len() <= tal_index {
            self.tals.push(Default::default())
        }
        self.tals[tal_index] += metrics;

        self.publication += metrics;
    }

    /// Adds a log book.
    pub fn append_log(&mut self, uri: uri::Rsync, book: LogBook) {
        self.log_books.push((uri, book))
    }

    /// Prepares the final metrics.
    pub fn prepare_final(&self, target: &mut Metrics) {
        let mut indexes: Vec<_>
            = self.repository_indexes.lock().unwrap().iter().map(|item| {
                (item.0.clone(), *item.1)
            }).collect();
        indexes.sort_by_key(|(_, idx)| *idx);
        target.repositories = indexes.into_iter().map(|(uri, _)| {
            RepositoryMetrics::new(uri)
        }).collect();
    }

    /// Collapse into the final metrics.
    ///
    /// Assumes that the target has been extended to fit all TALs and
    /// repositories.
    ///
    /// This only collapses the publication metrics since those are the ones
    /// collected by the engine.
    pub fn collapse(mut self, target: &mut Metrics) {
        for (target, metric) in target.tals.iter_mut().zip(self.tals) {
            target.publication += metric
        }
        for (target, metric) in target.repositories.iter_mut().zip(
            self.repositories
        ) {
            target.publication += metric
        }
        target.publication += self.publication;
        target.pub_point_logs.append(&mut self.log_books);
    }
}


//------------ ProcessRun ----------------------------------------------------

/// A type that can process the valid data from the RPKI.
pub trait ProcessRun: Send + Sync {
    /// The type processing the valid data of a single publication point.
    type PubPoint: ProcessPubPoint;

    /// Processes the given trust anchor.
    ///
    /// If the method wants the content of this trust anchor to be validated
    /// and processed, it returns a processor for it as some success value.
    /// If it rather wishes to skip this trust anchor, it returns `Ok(None)`.
    /// If it wishes to abort processing, it returns an error.
    ///
    /// The `tal_index` argument indicates the index of the TAL in the
    /// metrics produced by the processing run. Similarly, the
    /// `repository_index` argument refers to the index of the repository 
    /// publishing the trust anchor CA’s publication point in the metrics.
    fn process_ta(
        &self, tal: &Tal, uri: &TalUri, cert: &CaCert, tal_index: usize
    ) -> Result<Option<Self::PubPoint>, Failed>;
}


//------------ ProcessPubPoint -----------------------------------------------

/// A type that can process the valid data from an RPKI publication point.
pub trait ProcessPubPoint: Sized + Send + Sync {
    /// Sets the index of repository in the processing run metrics.
    fn repository_index(&mut self, repository_index: usize) {
        let _ = repository_index;
    }

    /// Process the publication points’s validity.
    ///
    /// The validity of the manifest’s EE certificate is provided in
    /// `manifest_ee`. The smaller of the manifest’s and CRL’s next update
    /// time is given in `stale`.
    fn point_validity(
        &mut self,
        manifest_ee: Validity,
        stale: Time,
    ) {
        let _ = (manifest_ee, stale);
    }

    /// Processes detached objects.
    ///
    /// The method is given the CA certificate and a way to check if
    /// a certificate issued by the CA has been revoked.
    fn process_detached<F>(
        &mut self,
        cert: &CaCert,
        check_crl: F
    ) -> Result<(), Failed>
    where F: Fn(&Cert) -> Result<(), ValidationError> {
        let _ = (cert, check_crl);
        Ok(())
    }

    /// Determines whether an object with the given URI should be processed.
    ///
    /// The object will only be processed if the method returns `Ok(true)`.
    /// If it returns `Ok(false)`, the object will be skipped quietly. If it
    /// returns an error, the entire processing run will be aborted.
    fn want(&self, uri: &uri::Rsync) -> Result<bool, Failed>;
   
    /// Process the content of a validated CA.
    ///
    /// The method can choose how to proceed. If it chooses to process the CA,
    /// it returns `Ok(Some(value))` with a new processor to be used for this
    /// CA. If it wishes to skip this CA, it returns `Ok(None)`. And if it
    /// wishes to abort processing, it returns an error.
    ///
    /// The `repository_index` argument indicates the index of the repository
    /// publishing the CA’s publication point in the metrics produced by the
    /// processing run.
    fn process_ca(
        &mut self, uri: &uri::Rsync, cert: &CaCert,
    ) -> Result<Option<Self>, Failed>;

    /// Process the content of a validated router certificate.
    ///
    /// The method is given both the URI and the certificate. If it
    /// returns an error, the entire processing run will be aborted.
    fn process_router_cert(
        &mut self, uri: &uri::Rsync, cert: Cert, ca_cert: &CaCert,
    ) -> Result<(), Failed> {
        let _ = (uri, cert, ca_cert);
        Ok(())
    }
 
    /// Process the content of a validated ROA.
    ///
    /// The method is given both the URI and the content of the ROA. If it
    /// returns an error, the entire processing run will be aborted.
    fn process_roa(
        &mut self,
        uri: &uri::Rsync,
        cert: ResourceCert,
        route: RouteOriginAttestation
    ) -> Result<(), Failed> {
        let _ = (uri, cert, route);
        Ok(())
    }

    /// Process the content of a validated ASPA object.
    ///
    /// The method is given both the URI and the content of the ASPA object.
    /// If it returns an error, the entire processing run will be aborted.
    fn process_aspa(
        &mut self,
        uri: &uri::Rsync,
        cert: ResourceCert,
        aspa: AsProviderAttestation,
    ) -> Result<(), Failed> {
        let _ = (uri, cert, aspa);
        Ok(())
    }
 
    /// Process the content of a Ghostbuster Record.
    ///
    /// The method is given both the URI and the raw content of the object
    /// as we currently don’t support parsing of these records.
    ///
    /// If the method returns an error, the entire processing run will be
    /// aborted.
    fn process_gbr(
        &mut self,
        uri: &uri::Rsync,
        cert: ResourceCert,
        content: Bytes
    ) -> Result<(), Failed> {
        let _ = (uri, cert, content);
        Ok(())
    }

    /// Restart processing with an empty data set.
    ///
    /// The method is called if processing has to switch to a different
    /// object set for a publication point. An implementation must drop all
    /// data collected so far and start with an empty set again.
    ///
    /// The method does not indicate whether processing has succeeded or
    /// failed.
    fn restart(&mut self) -> Result<(), Failed>;

    /// Completes processing of the CA.
    ///
    /// The method is called when all objects of the CA have been processed
    /// successfully or have been actively ignored and no error has happend.
    fn commit(self);

    /// Completes processing of an invalid CA.
    ///
    /// The method is called when at least one of the objects published by the
    /// CA is invalid.
    ///
    /// The default implementation does nothing at all.
    fn cancel(self, _cert: &CaCert) {
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use std::str::FromStr;
    use rpki::crypto::{PublicKeyFormat, Signer};
    use rpki::crypto::softsigner::{KeyId, SoftSigner};
    use rpki::repository::cert::{Overclaim, TbsCert};
    use rpki::repository::resources::{Asn, Prefix};
    use rpki::util::base64;
    use crate::payload::ValidationReport;
    use crate::utils::uri::UriExt;
    use super::*;

    #[test]
    fn dump_empty_cache() {
        let _ = crate::process::Process::init(); // May be inited already.
        let src = tempfile::tempdir().unwrap();
        let target = tempfile::tempdir().unwrap();
        let target = target.path().join("dump");
        let mut config = Config::default_with_paths(
            Default::default(), src.path().into()
        );
        config.rsync_command = "echo".into();
        config.rsync_args = Some(vec!["some".into()]);
        let engine = Engine::new(&config, true).unwrap();
        engine.dump(&target).unwrap();
    }


    //--- Trust anchor certificate selection

    const HTTPS_URI: &str = "https://example.com/ta/ta.cer";
    const RSYNC_URI: &str = "rsync://example.com/ta/ta.cer";

    /// Returns the start of the given year.
    fn year(year: i32) -> Time {
        Time::utc(year, 1, 1, 0, 0, 0)
    }

    /// Returns the time the selection tests happen at.
    fn now() -> Time {
        year(2030)
    }

    /// A trust anchor key with a TAL for it.
    struct TestTa {
        signer: SoftSigner,
        key: KeyId,
        tal: Tal,
    }

    impl TestTa {
        /// Creates a new key and a TAL with the given URIs for it.
        fn new(uris: &[&str]) -> Self {
            let signer = SoftSigner::new();
            let key = signer.create_key(PublicKeyFormat::Rsa).unwrap();
            let tal = Self::make_tal(&signer, &key, "test", uris);
            TestTa { signer, key, tal }
        }

        /// Creates a TAL with the given name and URIs for a key.
        fn make_tal(
            signer: &SoftSigner, key: &KeyId, name: &str, uris: &[&str]
        ) -> Tal {
            let pubkey = signer.get_key_info(key).unwrap();
            let mut tal = String::new();
            for uri in uris {
                tal.push_str(uri);
                tal.push('\n');
            }
            tal.push('\n');
            tal.push_str(&base64::Xml.encode(&pubkey.to_info_bytes()));
            let tal = Tal::read_named(
                name.into(), &mut tal.as_bytes()
            ).unwrap();
            assert_eq!(tal.uris().len(), uris.len());
            tal
        }

        /// Creates another TAL for the key.
        fn named_tal(&self, name: &str, uris: &[&str]) -> Tal {
            Self::make_tal(&self.signer, &self.key, name, uris)
        }

        /// Creates a TA certificate valid from the start of a year to the
        /// start of another year.
        fn cert(
            &self, serial: u64, not_before: i32, not_after: i32
        ) -> Bytes {
            let pubkey = self.signer.get_key_info(&self.key).unwrap();
            let mut cert = TbsCert::new(
                serial.into(), pubkey.to_subject_name(),
                Validity::new(year(not_before), year(not_after)),
                None, pubkey, KeyUsage::Ca, Overclaim::Trim
            );
            cert.set_basic_ca(Some(true));
            cert.set_ca_repository(Some(
                uri::Rsync::from_str("rsync://example.com/repo/").unwrap()
            ));
            cert.set_rpki_manifest(Some(
                uri::Rsync::from_str(
                    "rsync://example.com/repo/ta.mft"
                ).unwrap()
            ));
            cert.build_v4_resource_blocks(|b| b.push(Prefix::new(0, 0)));
            cert.build_v6_resource_blocks(|b| b.push(Prefix::new(0, 0)));
            cert.build_as_resource_blocks(|b| b.push((Asn::MIN, Asn::MAX)));
            cert.into_cert(
                &self.signer, &self.key
            ).unwrap().to_captured().into_bytes()
        }

        /// Returns the key identifier of the key.
        fn key_id(&self) -> KeyIdentifier {
            self.tal.key_info().key_identifier()
        }
    }

    /// An engine atop an empty store.
    ///
    /// The engine has a collector that never retrieves anything.
    struct TestEngine {
        dir: tempfile::TempDir,
        config: Config,
        engine: Engine,
    }

    impl TestEngine {
        fn new() -> Self {
            let _ = crate::process::Process::init(); // May be inited already.
            let dir = tempfile::tempdir().unwrap();
            let mut config = Config::default_with_paths(
                Default::default(), dir.path().into()
            );
            config.disable_rsync = true;
            config.disable_rrdp = true;
            let engine = Engine::new(&config, true).unwrap();
            TestEngine { dir, config, engine }
        }

        /// Starts a regular run.
        fn run(&self) -> Run<'_, ()> {
            self.run_with(())
        }

        /// Starts a regular run with the given processor.
        fn run_with<P>(&self, processor: P) -> Run<'_, P> {
            Run::new(
                &self.engine,
                self.engine.collector.as_ref().map(Collector::start),
                self.engine.store.start(), processor, false
            )
        }

        /// Starts a run without a collector.
        ///
        /// This is what the initial quick validation and a run with updates
        /// disabled use.
        fn offline_run(&self) -> Run<'_, ()> {
            Run::new(
                &self.engine, None, self.engine.store.start(), (), false
            )
        }

        /// Returns the path of the TA certificate stored for a key.
        fn key_path(&self, ta: &TestTa) -> PathBuf {
            self.dir.path().join("stored/ta/key").join(
                format!("{}.cer", ta.key_id()).to_lowercase()
            )
        }

        /// Returns the path earlier versions stored a TA certificate under.
        fn legacy_path(&self, uri: &str) -> PathBuf {
            self.dir.path().join("stored").join(
                match TalUri::from_str(uri).unwrap() {
                    TalUri::Rsync(uri) => uri.unique_path("ta/rsync", ".cer"),
                    TalUri::Https(uri) => uri.unique_path("ta/https", ".cer"),
                }
            )
        }

        /// Stores a TA certificate the way earlier versions did.
        fn store_legacy(&self, uri: &str, content: &[u8]) {
            let path = self.legacy_path(uri);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, content).unwrap();
        }
    }

    /// Stores a TA certificate for the key of the TAL.
    fn store(run: &Run<()>, ta: &TestTa, content: &[u8]) {
        run.store.update_ta(ta.key_id(), content).unwrap()
    }

    /// Returns the TA certificate stored for the key of the TAL.
    fn stored(run: &Run<()>, ta: &TestTa) -> Option<Bytes> {
        run.store.load_ta(ta.key_id()).unwrap()
    }

    /// Selects the TA certificate for the TAL.
    ///
    /// The fetched certificate, if given, needs to be valid. It will have
    /// the last URI of the TAL, so it can be told apart from the cached
    /// certificate which has the first.
    ///
    /// Returns the selected certificate and its URI.
    fn select(
        run: &Run<()>, ta: &TestTa, fetched: Option<&Bytes>
    ) -> Option<(Bytes, String)> {
        let task = TalTask { tal: &ta.tal, index: 0 };
        let fetched = fetched.map(|bytes| {
            run.check_ta(
                bytes.clone(), &task, ta.tal.uris().last().unwrap(), now()
            ).unwrap()
        });
        run.select_ta(&task, fetched, now()).unwrap().map(|cert| {
            (cert.cert().to_captured().into_bytes(), cert.uri().to_string())
        })
    }

    #[test]
    fn reload_tals_skips_tals_with_same_key() {
        let mut env = TestEngine::new();
        let ta = TestTa::new(&[HTTPS_URI]);
        let other = TestTa::new(&[HTTPS_URI]);
        env.engine.extra_tals_dir = None;
        env.engine.bundled_tals = vec![
            other.named_tal("delta", &[HTTPS_URI]),
            ta.named_tal("charlie", &[RSYNC_URI]),
            ta.named_tal("alpha", &[HTTPS_URI]),
            ta.named_tal("bravo", &[HTTPS_URI]),
        ];
        env.engine.reload_tals().unwrap();

        // The first TAL by name wins.
        assert_eq!(
            env.engine.tals.iter().map(|tal| {
                tal.info().name()
            }).collect::<Vec<_>>(),
            ["alpha", "delta"]
        );
    }

    #[test]
    fn ta_preferred_order() {
        use super::TaPreference::{ExpiresEarlier, IssuedLater};

        fn preferred(
            left: (i32, i32), right: (i32, i32)
        ) -> Option<TaPreference> {
            ta_preferred(
                Validity::new(year(left.0), year(left.1)),
                Validity::new(year(right.0), year(right.1)),
            )
        }

        // The later notBefore is preferred, whatever notAfter is.
        assert_eq!(preferred((2021, 2040), (2020, 2040)), Some(IssuedLater));
        assert_eq!(preferred((2020, 2040), (2021, 2040)), None);
        assert_eq!(preferred((2021, 2050), (2020, 2040)), Some(IssuedLater));
        assert_eq!(preferred((2021, 2035), (2020, 2040)), Some(IssuedLater));
        assert_eq!(preferred((2020, 2035), (2021, 2040)), None);
        assert_eq!(preferred((2020, 2050), (2021, 2040)), None);

        // With the same notBefore, the earlier notAfter is preferred.
        assert_eq!(
            preferred((2020, 2035), (2020, 2040)), Some(ExpiresEarlier)
        );
        assert_eq!(preferred((2020, 2040), (2020, 2035)), None);

        // With the same validity, there is no preference.
        assert_eq!(preferred((2020, 2040), (2020, 2040)), None);
    }

    #[test]
    fn check_ta_cert_rejects() {
        let ta = TestTa::new(&[HTTPS_URI]);
        let other = TestTa::new(&[HTTPS_URI]);
        let check = |bytes| check_ta_cert(bytes, &ta.tal, true, now());

        let cert = ta.cert(1, 2020, 2040);
        assert!(check(cert.clone()).is_ok());

        // Garbage and a partial certificate.
        assert!(matches!(
            check(Bytes::from_static(b"garbage")),
            Err(TaCertError::Decode)
        ));
        assert!(matches!(
            check(cert.slice(..cert.len() - 10)),
            Err(TaCertError::Decode)
        ));

        // A valid TA certificate for some other key.
        assert!(matches!(
            check(other.cert(1, 2020, 2040)),
            Err(TaCertError::KeyMismatch)
        ));

        // Expired and not yet valid.
        assert!(matches!(
            check(ta.cert(1, 2020, 2029)),
            Err(TaCertError::Invalid(_))
        ));
        assert!(matches!(
            check(ta.cert(1, 2031, 2040)),
            Err(TaCertError::Invalid(_))
        ));
    }

    #[test]
    fn ta_fetched_without_cache() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let cert = ta.cert(1, 2020, 2040);

        assert_eq!(stored(&run, &ta), None);
        assert_eq!(
            select(&run, &ta, Some(&cert)),
            Some((cert.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));
        assert!(env.key_path(&ta).is_file());
    }

    #[test]
    fn ta_cached_without_fetch() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let cert = ta.cert(1, 2020, 2040);
        store(&run, &ta, &cert);

        assert_eq!(
            select(&run, &ta, None),
            Some((cert.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));
    }

    #[test]
    fn ta_without_fetch_and_cache() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);

        assert_eq!(select(&run, &ta, None), None);
        assert_eq!(stored(&run, &ta), None);
    }

    #[test]
    fn ta_newer_fetched_replaces_cache() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        store(&run, &ta, &ta.cert(1, 2020, 2040));

        // A later notBefore wins …
        let cert = ta.cert(2, 2021, 2040);
        assert_eq!(
            select(&run, &ta, Some(&cert)),
            Some((cert.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));

        // … even if the certificate has a longer validity.
        let cert = ta.cert(3, 2022, 2050);
        assert_eq!(
            select(&run, &ta, Some(&cert)),
            Some((cert.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));
    }

    #[test]
    fn ta_older_fetched_ignored() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let cached = ta.cert(2, 2021, 2040);
        store(&run, &ta, &cached);

        // An earlier notBefore loses …
        assert_eq!(
            select(&run, &ta, Some(&ta.cert(1, 2020, 2040))),
            Some((cached.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cached.clone()));

        // … even if the certificate has a shorter validity.
        assert_eq!(
            select(&run, &ta, Some(&ta.cert(3, 2020, 2035))),
            Some((cached.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cached));
    }

    #[test]
    fn ta_shorter_validity_preferred() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let cached = ta.cert(1, 2020, 2040);
        store(&run, &ta, &cached);

        // Same notBefore, later notAfter: the cached certificate stays.
        assert_eq!(
            select(&run, &ta, Some(&ta.cert(2, 2020, 2045))),
            Some((cached.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cached));

        // Same notBefore, earlier notAfter: the fetched certificate wins.
        let cert = ta.cert(3, 2020, 2035);
        assert_eq!(
            select(&run, &ta, Some(&cert)),
            Some((cert.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));
    }

    #[test]
    fn ta_equal_validity_prefers_fetched() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let cached = ta.cert(1, 2020, 2040);
        store(&run, &ta, &cached);

        let cert = ta.cert(2, 2020, 2040);
        assert_ne!(cert, cached);
        assert_eq!(
            select(&run, &ta, Some(&cert)),
            Some((cert.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cert));
    }

    #[test]
    fn ta_invalid_cache_ignored() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let other = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let fetched = ta.cert(1, 2020, 2040);

        // All of the certificates would be preferred over the fetched one
        // if only they were valid.
        for cached in [
            // Expired.
            ta.cert(2, 2025, 2029),
            // Not yet valid.
            ta.cert(2, 2031, 2040),
            // Wrong key.
            other.cert(2, 2025, 2040),
            // Not a certificate.
            Bytes::from_static(b"garbage"),
        ] {
            store(&run, &ta, &cached);
            assert_eq!(select(&run, &ta, None), None);
            assert_eq!(stored(&run, &ta), Some(cached));
            assert_eq!(
                select(&run, &ta, Some(&fetched)),
                Some((fetched.clone(), RSYNC_URI.into()))
            );
            assert_eq!(stored(&run, &ta), Some(fetched.clone()));
        }
    }

    #[test]
    fn ta_offline_run_leaves_store_alone() {
        let env = TestEngine::new();
        let run = env.offline_run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);

        // A legacy certificate is used but not stored by key.
        let legacy = ta.cert(1, 2020, 2040);
        env.store_legacy(RSYNC_URI, &legacy);
        assert_eq!(
            select(&run, &ta, None),
            Some((legacy.clone(), HTTPS_URI.into()))
        );
        assert!(!env.dir.path().join("stored/ta/key").exists());
        assert!(!env.dir.path().join("stored/tmp").exists());

        // Neither is a fetched certificate, even if a run without a
        // collector never has one.
        let fetched = ta.cert(2, 2021, 2040);
        assert_eq!(
            select(&run, &ta, Some(&fetched)),
            Some((fetched, RSYNC_URI.into()))
        );
        assert!(!env.dir.path().join("stored/ta/key").exists());
        assert!(!env.dir.path().join("stored/tmp").exists());

        // The certificate stored by key is used and left as it is.
        let cached = ta.cert(3, 2022, 2040);
        store(&run, &ta, &cached);
        assert_eq!(
            select(&run, &ta, None),
            Some((cached.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cached));
    }

    #[test]
    fn ta_legacy_seeds_store() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let https = ta.cert(1, 2020, 2040);
        let rsync = ta.cert(2, 2021, 2040);
        env.store_legacy(HTTPS_URI, &https);
        env.store_legacy(RSYNC_URI, &rsync);

        // The preferred legacy certificate is selected and stored by key.
        assert_eq!(
            select(&run, &ta, None),
            Some((rsync.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(rsync));
    }

    #[test]
    fn ta_legacy_competes_with_fetched() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);
        let legacy = ta.cert(2, 2021, 2040);
        env.store_legacy(HTTPS_URI, &legacy);

        assert_eq!(
            select(&run, &ta, Some(&ta.cert(1, 2020, 2040))),
            Some((legacy.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(legacy));
    }

    #[test]
    fn ta_legacy_ignored_once_stored() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);

        // The legacy certificate would be preferred over everything else.
        env.store_legacy(HTTPS_URI, &ta.cert(9, 2025, 2040));

        // A valid certificate stored by key is used.
        let cached = ta.cert(1, 2020, 2040);
        store(&run, &ta, &cached);
        assert_eq!(
            select(&run, &ta, None),
            Some((cached.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(cached));

        // The legacy certificate doesn’t come back if what is stored by
        // key can’t be used any more.
        for cached in [
            // Expired.
            ta.cert(2, 2020, 2029),
            // Not a certificate.
            Bytes::from_static(b"garbage"),
        ] {
            store(&run, &ta, &cached);
            assert_eq!(select(&run, &ta, None), None);
            assert_eq!(stored(&run, &ta), Some(cached));
        }

        // A fetched certificate only competes with what is stored by key.
        let fetched = ta.cert(3, 2021, 2040);
        assert_eq!(
            select(&run, &ta, Some(&fetched)),
            Some((fetched.clone(), RSYNC_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(fetched));
    }

    #[test]
    fn ta_unreadable_legacy_ignored() {
        let env = TestEngine::new();
        let mut run = env.run();
        let ta = TestTa::new(&[HTTPS_URI, RSYNC_URI]);

        // A directory in place of the legacy certificate can’t be read.
        fs::create_dir_all(env.legacy_path(HTTPS_URI)).unwrap();
        assert_eq!(select(&run, &ta, None), None);

        // The other legacy certificate is still used.
        let legacy = ta.cert(1, 2020, 2090);
        env.store_legacy(RSYNC_URI, &legacy);
        assert_eq!(
            select(&run, &ta, None),
            Some((legacy.clone(), HTTPS_URI.into()))
        );
        assert_eq!(stored(&run, &ta), Some(legacy));

        // Cleanup doesn’t trip over it either.
        run.cleanup().unwrap();
        assert!(!env.legacy_path(HTTPS_URI).exists());
    }

    #[test]
    fn ta_cleanup() {
        const SEED_URI: &str = "https://seed.example.com/ta.cer";
        const EXPIRED_SEED_URI: &str = "https://old-seed.example.com/ta.cer";
        const STORED_URI: &str = "https://stored.example.com/ta.cer";
        const EXPIRED_URI: &str = "rsync://expired.example.com/ta/ta.cer";
        const GARBAGE_URI: &str = "rsync://garbage.example.com/ta/ta.cer";

        let env = TestEngine::new();
        let mut run = env.run();

        // Cleanup uses the real time, so the certificates need to be valid
        // both then and at the time of the tests.

        // A legacy certificate with nothing stored for its key.
        let seed = TestTa::new(&[SEED_URI]);
        let seed_cert = seed.cert(1, 2020, 2090);
        env.store_legacy(SEED_URI, &seed_cert);

        // The same but the legacy certificate has expired.
        let expired_seed = TestTa::new(&[EXPIRED_SEED_URI]);
        env.store_legacy(
            EXPIRED_SEED_URI, &expired_seed.cert(1, 2020, 2021)
        );

        // A legacy certificate with a valid certificate stored for its key.
        let stored_ta = TestTa::new(&[STORED_URI]);
        let stored_cert = stored_ta.cert(2, 2021, 2090);
        env.store_legacy(STORED_URI, &stored_ta.cert(1, 2020, 2090));
        store(&run, &stored_ta, &stored_cert);

        // A legacy certificate with an expired certificate stored for its
        // key.
        let expired = TestTa::new(&[EXPIRED_URI]);
        env.store_legacy(EXPIRED_URI, &expired.cert(1, 2020, 2090));
        store(&run, &expired, &expired.cert(2, 2020, 2021));

        // A legacy file that isn’t a certificate.
        env.store_legacy(GARBAGE_URI, b"garbage");

        run.cleanup().unwrap();

        // The legacy certificate is kept for as long as it is needed.
        assert!(env.legacy_path(SEED_URI).is_file());
        assert!(!env.legacy_path(EXPIRED_SEED_URI).exists());
        assert!(!env.legacy_path(GARBAGE_URI).exists());

        // A legacy certificate is removed once something is stored for its
        // key.
        assert!(!env.legacy_path(STORED_URI).exists());
        assert_eq!(stored(&run, &stored_ta), Some(stored_cert));

        // If that has expired, it is removed, too, and the legacy
        // certificate doesn’t come back.
        assert!(!env.legacy_path(EXPIRED_URI).exists());
        assert!(!env.key_path(&expired).exists());
        assert_eq!(select(&run, &expired, None), None);

        // Once the remaining legacy certificate has been selected and thus
        // stored by key, it is removed, too.
        assert_eq!(
            select(&run, &seed, None),
            Some((seed_cert.clone(), SEED_URI.into()))
        );
        run.cleanup().unwrap();
        assert!(!env.dir.path().join("stored/ta/https").exists());
        assert!(!env.dir.path().join("stored/ta/rsync").exists());
        assert_eq!(stored(&run, &seed), Some(seed_cert));
        assert!(env.key_path(&stored_ta).is_file());
    }

    #[test]
    fn ta_no_uris() {
        let env = TestEngine::new();
        let run = env.run();
        let ta = TestTa::new(&[]);
        store(&run, &ta, &ta.cert(1, 2020, 2040));

        assert_eq!(select(&run, &ta, None), None);
    }

    #[test]
    fn ta_store_failure_fails_run() {
        let env = TestEngine::new();
        let ta = TestTa::new(&[HTTPS_URI]);
        let report = ValidationReport::new(&env.config);
        let run = env.run_with(&report);

        // A directory in place of the stored certificate can’t be read.
        fs::create_dir_all(env.key_path(&ta)).unwrap();

        assert!(
            run.process_tal_task(
                TalTask { tal: &ta.tal, index: 0 },
                &SegQueue::new(), &mut RunMetrics::default(),
            ).is_err()
        );
        assert!(run.had_err.load(Ordering::Relaxed));
        assert!(run.is_fatal.load(Ordering::Relaxed));
    }
}

