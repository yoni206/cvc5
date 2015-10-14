# CVC4_CHECK_FOR_CRYPTOMINISAT
# ------------------
# Look for cryptominisat and link it in, but only if user requested.
AC_DEFUN([CVC4_CHECK_FOR_CRYPTOMINISAT], [
AC_MSG_CHECKING([whether user requested cryptominisat support])

have_libcryptominisat=0
CRYPTOMINISAT_LIBS=
CRYPTOMINISAT_LDFLAGS=
     
have_libcryptominisat=0
if test "$with_cryptominisat" = no; then
  AC_MSG_RESULT([no, cryptominisat disabled by user])
elif test -n "$with_cryptominisat"; then
  AC_MSG_RESULT([yes, cryptominisat requested by user])
  AC_ARG_VAR(CRYPTOMINISAT_HOME, [path to top level of cryptominisat source tree])
  AC_ARG_WITH(
    [cryptominisat-dir],
    AS_HELP_STRING(
      [--with-cryptominisat-dir=PATH],
      [path to top level of cryptominisat source tree]
    ),
    [CRYPTOMINISAT_HOME="$withval"],
    [ if test -z "$CRYPTOMINISAT_HOME"; then
        AC_MSG_FAILURE([must give --with-cryptominisat-dir=PATH or define environment variable CRYPTOMINISAT_HOME!])
      fi
    ]
  )

  if ! test -d "$CRYPTOMINISAT_HOME" || ! test -x "$CRYPTOMINISAT_HOME/bin/cryptominisat" ; then
    AC_MSG_FAILURE([either $CRYPTOMINISAT_HOME is not an cryptominisat install tree or it's not yet built])
  fi

  AC_LANG(C++)
  cvc4_save_LIBS="$LIBS"
  cvc4_save_LDFLAGS="$LDFLAGS"
  cvc4_save_CPPFLAGS="$CPPFLAGS"

  CRYPTOMINISAT_LDFLAGS="-L$CRYPTOMINISAT_HOME/lib"
  CRYPTOMINISAT_LIBS="-lcryptominisat4 -lm4ri"

  LDFLAGS="$LDFLAGS $CRYPTOMINISAT_LDFLAGS"
  LIBS="$LIBS $CRYPTOMINISAT_LIBS"
  
  CPPFLAGS="$CPPFLAGS -I$CRYPTOMINISAT_HOME/include"

  AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([#include <cryptominisat4/cryptominisat.h>],
      [CMSat::SATSolver test()])], [have_libcryptominisat=1],
    [AC_MSG_ERROR([libcryptominisat is not installed.])])

  LDFLAGS="$cvc4_save_LDFLAGS"
  CPPFLAGS="$cvc4_save_CPPFLAGS"
  LIBS="$cvc4_save_LIBS"
else
  AC_MSG_RESULT([no, user didn't request cryptominisat])
  with_cryptominisat=no
fi

])# CVC4_TRY_STATIC_CRYPTOMINISAT_WITH
