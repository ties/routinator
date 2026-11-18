Dumping Stored Data
===================

The :subcmd:`dump` subcommand writes the contents of all stored data to the file
system. This is primarily intended for debugging but can be used to get access
to the view of the RPKI data that Routinator currently sees. This subcommand has
only one option, :option:`--output`, which specifies the directory where the
output should be written.
   
Three directories will be created in the output directory:

rrdp
    This directory contains all the files collected via RRDP from the various
    repositories. Each repository is stored in its own directory. The mapping
    between ``rpkiNotify`` URI and path is provided in the
    :file:`repositories.json` file. For each repository, the files are stored in
    a directory structure based on the components of the file as rsync URI.

rsync
    This directory contains all the files collected via rsync. The files are
    stored in a directory structure based on the components of the file's rsync
    URI.

store
    This directory contains all the files used for validation. Files collected
    via RRDP or rsync are copied to the store if they are correctly referenced
    by a valid manifest. This part contains one directory for each RRDP
    repository similarly structured to the :file:`rrdp` directory and one
    additional directory :file:`rsync` that contains files collected via rsync.

ta
    This directory contains the trust anchor certificates. There is one
    certificate for each trust anchor key. It is stored in the directory
    :file:`key` in a file that has the hexadecimal encoding of the
    certificate’s subject key identifier as the file name with the
    extension ``.cer`` appended.

    Certificates stored by earlier versions of Routinator are kept in the
    directories :file:`https` and :file:`rsync`. Such a certificate is
    removed once a certificate has been stored for its key or once it has
    expired.

.. versionadded:: 0.9.0
.. versionchanged:: 0.11.1
   Stored trust anchor certificates are dumped into the ``ta`` directory.
.. versionchanged:: 0.16.2
   Trust anchor certificates are stored by key rather than by URI.

