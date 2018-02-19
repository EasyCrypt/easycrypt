set ECPATH=%~dp0
set PATH=%ECPATH%\bin;%PATH%

share\emacs\bin\runemacs.exe -l share/easycrypt/pg/ProofGeneral/generic/proof-site.el -l share\easycrypt\pg\emacs.rc --no-init-file --no-site-file --debug-init
