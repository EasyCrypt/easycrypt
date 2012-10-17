AC_INIT([easycrypt],[1.0])



AC_CHECK_TOOL([OCAML],[ocaml],[no])
if test "$OCAML" = "no"; then
	AC_MSG_ERROR([ocaml top level not found])
fi

AC_CHECK_TOOL([OCAMLC],[ocamlc],[no])
if test "$OCAMLC" = "no"; then
	AC_MSG_ERROR([ocamlc not found])
fi

dnl we extract Ocaml version number and library path
OCAMLVERSION=`$OCAMLC -v | sed -n -e 's|.*version *\(.*\)$|\1|p' `
echo "ocaml version is $OCAMLVERSION"
OCAMLLIB=`$OCAMLC -v | tail -1 | cut -f 4 -d " " | sed 's/\/\//\//g'`
echo "ocaml library path is $OCAMLLIB"

AC_CHECK_PROG(OCAMLCDOTOPT,ocamlc.opt,ocamlc.opt,no)
if test "$OCAMLCDOTOPT" != no ; then
	AC_MSG_CHECKING(ocamlc.opt version)
	TMPVERSION=`$OCAMLCDOTOPT -v | sed -n -e 's|.*version* *\(.*\)$|\1|p' `
	if test "$TMPVERSION" != "$OCAMLVERSION" ; then
	    AC_MSG_RESULT(differs from ocamlc; ocamlc.opt discarded.)
	else
	    AC_MSG_RESULT(ok)
	    OCAMLC=$OCAMLCDOTOPT
	fi
fi


AC_CHECK_TOOL([OCAMLDEP],[ocamldep],[no])
if test "$OCAMLDEP" = "no"; then
	AC_MSG_ERROR([ocamldep not found])
fi

AC_CHECK_TOOL([OCAMLMKTOP],[ocamlmktop],[no])
if test "$OCAMLMKTOP" = "no"; then
	AC_MSG_ERROR([ocamlmktop not found])
fi

AC_CHECK_TOOL([OCAMLLEX],[ocamllex],[no])
if test "$OCAMLLEX" = "no"; then
	AC_MSG_ERROR([OcamlLex not found])
fi

AC_CHECK_TOOL([MENHIR],[menhir],[no])
if test "$MENHIR" = "no"; then
	AC_MSG_ERROR([Menhir not found])
fi
MENHIRLIBS="+menhirLib"

AC_CHECK_TOOL([OCAMLYACC],[ocamlyacc],[no])
if test "$OCAMLYACC" = "no"; then
	AC_MSG_ERROR([OcamlYacc not found])
fi

#AC_CHECK_TOOL([OCAMLFIND],[ocamlfind],[no])
#if test "$OCAMLFIND" = "no"; then
#	AC_MSG_ERROR([Ocamlfind not found])
#fi

AC_CHECK_PROG(OCAMLDOC,ocamldoc,ocamldoc,true)
if test "$OCAMLDOC" = true ; then
    AC_MSG_ERROR(Cannot find ocamldoc)
fi

AC_ARG_WITH(proof-general,
	AS_HELP_STRING([--with-proof-general=PATH],
						[specify the path to install EasyCrypt mode for Proof General)]),
	PROOF_GENERAL_PATH="$withval")

if [[ "x$PROOF_GENERAL_PATH" = "x" ]]; then
	AC_CHECK_FILE(/usr/share/emacs/site-lisp/ProofGeneral/generic/proof-site.el,PG=yes,PG=no)
	PROOF_GENERAL_PATH=/usr/share/emacs/site-lisp/ProofGeneral
else
   echo "Path of ProofGeneral [$PROOF_GENERAL_PATH]"
	AC_CHECK_FILE($PROOF_GENERAL_PATH/generic/proof-site.el,PG=yes,PG=no)
fi

if test "$PG" = "no"; then
	AC_MSG_WARN(Cannot find ProofGeneral folder in default location. 
   (It can be specified with the option --with-proof-general=PATH))
	WITH_EMACS=no
else
	WITH_EMACS=yes
fi



## is ocamlfind installed and compatible?
AC_CHECK_PROG(USEOCAMLFIND,ocamlfind,yes,no)

if test "$USEOCAMLFIND" = yes; then
   OCAMLFINDLIB=$(ocamlfind printconf stdlib)
   OCAMLFIND=$(which ocamlfind)
   if test "$OCAMLFINDLIB" != "$OCAMLLIB"; then
   USEOCAMLFIND=no;
   echo "but your ocamlfind is not compatible with your ocamlc:"
   echo "ocamlfind : $OCAMLFINDLIB, ocamlc : $OCAMLLIB"
   fi
fi


LIBS=yes
AC_CHECK_FILE($OCAMLLIB/unix.cma,,LIBS=no)
AC_CHECK_FILE($OCAMLLIB/str.cma,,LIBS=no)
AC_CHECK_FILE($OCAMLLIB/nums.cma,,LIBS=no)
AC_CHECK_FILE($OCAMLLIB/dynlink.cma,,LIBS=no)
if test "$USEOCAMLFIND" = yes; then
  OCAMLGRAPHLIB=$(ocamlfind query ocamlgraph 2>/dev/null)
  WHY3LIB=$(ocamlfind query why3 2>/dev/null)
fi


if test -n "$OCAMLGRAPHLIB"; then
  echo "ocamlfind found ocamlgraph in $OCAMLGRAPHLIB"
else
  OCAMLGRAPHLIB="+ocamlgraph"
  AC_CHECK_FILE($OCAMLLIB/ocamlgraph/graph.cma,,LIBS=no)
fi

if test -n "$WHY3LIB"; then
  echo "ocamlfind found why3 in $WHY3LIB"
else
  WHY3LIB="+why3"
  AC_CHECK_FILE($OCAMLLIB/why3/why3.cma,,LIBS=no)
fi

if test "$LIBS" = "no"; then
	AC_MSG_ERROR([Cannot find the necessaries libraries])
fi




AC_ARG_ENABLE(tools,
AS_HELP_STRING([--enable-tools],
					[enable tools ]),,
					enable_tools=yes)



AC_ARG_ENABLE(tests,
AS_HELP_STRING([--enable-tests],
					[enable tests ]),,
					enable_tests=yes)


AC_ARG_ENABLE(doc,
AS_HELP_STRING([--enable-doc],
					[enable doc]),,
					enable_doc=yes)


AC_SUBST([OCAMLC])
AC_SUBST([OCAML])
AC_SUBST([OCAMLDEP])
AC_SUBST([OCAMLMKTOP])
AC_SUBST([OCAMLLEX])
AC_SUBST([OCAMLYACC])
AC_SUBST([OCAMLFIND])
AC_SUBST([OCAMLDOC])
AC_SUBST([PROOF_GENERAL_PATH])
AC_SUBST([WITH_EMACS])
AC_SUBST([enable_tools])
AC_SUBST([enable_tests])
AC_SUBST([enable_doc])
AC_SUBST([OCAMLGRAPHLIB])
AC_SUBST([WHY3LIB])
AC_SUBST([MENHIR])
AC_SUBST([MENHIRLIBS])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
