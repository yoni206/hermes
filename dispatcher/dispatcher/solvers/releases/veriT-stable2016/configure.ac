AC_INIT(veriT, stable2016, verit-bugs@lists.gforge.inria.fr, http://www.verit-solver.org)

# ===========================================================================
#      http://www.gnu.org/software/autoconf-archive/ax_gcc_builtin.html
# ===========================================================================
#
# SYNOPSIS
#
#   AX_GCC_BUILTIN(BUILTIN)
#
# DESCRIPTION
#
#   This macro checks if the compiler supports one of GCC's built-in
#   functions; many other compilers also provide those same built-ins.
#
#   The BUILTIN parameter is the name of the built-in function.
#
#   If BUILTIN is supported define HAVE_<BUILTIN>. Keep in mind that since
#   builtins usually start with two underscores they will be copied over
#   into the HAVE_<BUILTIN> definition (e.g. HAVE___BUILTIN_EXPECT for
#   __builtin_expect()).
#
#   The macro caches its result in the ax_cv_have_<BUILTIN> variable (e.g.
#   ax_cv_have___builtin_expect).
#
#   The macro currently supports the following built-in functions:
#
#    __builtin_assume_aligned
#    __builtin_bswap32
#    __builtin_bswap64
#    __builtin_choose_expr
#    __builtin___clear_cache
#    __builtin_clrsb
#    __builtin_clrsbl
#    __builtin_clrsbll
#    __builtin_clz
#    __builtin_clzl
#    __builtin_clzll
#    __builtin_complex
#    __builtin_constant_p
#    __builtin_ctz
#    __builtin_ctzl
#    __builtin_ctzll
#    __builtin_expect
#    __builtin_ffs
#    __builtin_ffsl
#    __builtin_ffsll
#    __builtin_fpclassify
#    __builtin_huge_val
#    __builtin_huge_valf
#    __builtin_huge_vall
#    __builtin_inf
#    __builtin_infd128
#    __builtin_infd32
#    __builtin_infd64
#    __builtin_inff
#    __builtin_infl
#    __builtin_isinf_sign
#    __builtin_nan
#    __builtin_nand128
#    __builtin_nand32
#    __builtin_nand64
#    __builtin_nanf
#    __builtin_nanl
#    __builtin_nans
#    __builtin_nansf
#    __builtin_nansl
#    __builtin_object_size
#    __builtin_parity
#    __builtin_parityl
#    __builtin_parityll
#    __builtin_popcount
#    __builtin_popcountl
#    __builtin_popcountll
#    __builtin_powi
#    __builtin_powif
#    __builtin_powil
#    __builtin_prefetch
#    __builtin_trap
#    __builtin_types_compatible_p
#    __builtin_unreachable
#
#   Unsuppored built-ins will be tested with an empty parameter set and the
#   result of the check might be wrong or meaningless so use with care.
#
# LICENSE
#
#   Copyright (c) 2013 Gabriele Svelto <gabriele.svelto@gmail.com>
#
#   Copying and distribution of this file, with or without modification, are
#   permitted in any medium without royalty provided the copyright notice
#   and this notice are preserved.  This file is offered as-is, without any
#   warranty.

#serial 2

AC_DEFUN([AX_GCC_BUILTIN], [
    AS_VAR_PUSHDEF([ac_var], [ax_cv_have_$1])

    AC_CACHE_CHECK([for $1], [ac_var], [
        AC_LINK_IFELSE([AC_LANG_PROGRAM([], [
            m4_case([$1],
                [__builtin_assume_aligned], [$1("", 0)],
                [__builtin_bswap32], [$1(0)],
                [__builtin_bswap64], [$1(0)],
                [__builtin_choose_expr], [$1(0, 0, 0)],
                [__builtin___clear_cache], [$1("", "")],
                [__builtin_clrsb], [$1(0)],
                [__builtin_clrsbl], [$1(0)],
                [__builtin_clrsbll], [$1(0)],
                [__builtin_clz], [$1(0)],
                [__builtin_clzl], [$1(0)],
                [__builtin_clzll], [$1(0)],
                [__builtin_complex], [$1(0.0, 0.0)],
                [__builtin_constant_p], [$1(0)],
                [__builtin_ctz], [$1(0)],
                [__builtin_ctzl], [$1(0)],
                [__builtin_ctzll], [$1(0)],
                [__builtin_expect], [$1(0, 0)],
                [__builtin_ffs], [$1(0)],
                [__builtin_ffsl], [$1(0)],
                [__builtin_ffsll], [$1(0)],
                [__builtin_fpclassify], [$1(0, 1, 2, 3, 4, 0.0)],
                [__builtin_huge_val], [$1()],
                [__builtin_huge_valf], [$1()],
                [__builtin_huge_vall], [$1()],
                [__builtin_inf], [$1()],
                [__builtin_infd128], [$1()],
                [__builtin_infd32], [$1()],
                [__builtin_infd64], [$1()],
                [__builtin_inff], [$1()],
                [__builtin_infl], [$1()],
                [__builtin_isinf_sign], [$1(0.0)],
                [__builtin_nan], [$1("")],
                [__builtin_nand128], [$1("")],
                [__builtin_nand32], [$1("")],
                [__builtin_nand64], [$1("")],
                [__builtin_nanf], [$1("")],
                [__builtin_nanl], [$1("")],
                [__builtin_nans], [$1("")],
                [__builtin_nansf], [$1("")],
                [__builtin_nansl], [$1("")],
                [__builtin_object_size], [$1("", 0)],
                [__builtin_parity], [$1(0)],
                [__builtin_parityl], [$1(0)],
                [__builtin_parityll], [$1(0)],
                [__builtin_popcount], [$1(0)],
                [__builtin_popcountl], [$1(0)],
                [__builtin_popcountll], [$1(0)],
                [__builtin_powi], [$1(0, 0)],
                [__builtin_powif], [$1(0, 0)],
                [__builtin_powil], [$1(0, 0)],
                [__builtin_prefetch], [$1("")],
                [__builtin_trap], [$1()],
                [__builtin_types_compatible_p], [$1(int, int)],
                [__builtin_unreachable], [$1()],
                [m4_warn([syntax], [Unsupported built-in $1, the test may fail])
                 $1()]
            )
            ])],
            [AS_VAR_SET([ac_var], [yes])],
            [AS_VAR_SET([ac_var], [no])])
    ])

    AS_IF([test yes = AS_VAR_GET([ac_var])],
        [AC_DEFINE_UNQUOTED(AS_TR_CPP(HAVE_$1), 1,
            [Define to 1 if the system has the `$1' built-in function])], [])

    AS_VAR_POPDEF([ac_var])
])

# ===========================================================================
# end of ax_gcc_builtin
# ===========================================================================

CPPFLAGS=""

AC_ARG_ENABLE(proof,
  [  --disable-proof    disable proof-production],
  [PROOF_PRODUCTION=no],
  [PROOF_PRODUCTION=$enableval
   CPPFLAGS+=" -DPROOF"])

AC_ARG_ENABLE(natqsort,
  [  --enable-natqsort  use native quicksort],
  [CPPFLAGS+=" -DNATIVE_QSORT"])

AC_ARG_ENABLE(debug,
  [  --enable-debug     compile debugging version],
  [ARG_DEBUG="true"])

AC_ARG_ENABLE(debug-mem,
  [  --enable-debug-mem compile memory debugging version],
  [ARG_MEM="true"])

AC_ARG_ENABLE(prof,
  [  --enable-prof      compile profiling version],
  [ARG_PROF="true"])

AC_ARG_ENABLE(coverage,
  [  --enable-coverage  compile coverage],
  [ARG_COVERAGE="true"])

AC_ARG_ENABLE(static,
  [  --enable-static    static linking],
  [ARG_STATIC="true"])

AC_ARG_ENABLE(pedantic,
  [  --enable-pedantic  strong static check of code],
  [ARG_PEDANTIC="true"])

AC_ARG_ENABLE(strict,
  [  --enable-strict    stop on all errors],
  [ARG_STRICT="true"])

check_gcc_is_aliased_to_clang () {
   $as_echo_n "checking whether gcc has been aliased to clang... " >&6;
   # 2>&1 because Apple's clang writes some messages on stderr
   # we do not want that
   # -q options to grep makes it quiet
   r=`$1 --version 2>&1 | grep -q clang >&6`
   is_clang=$?
   if test "$is_clang" == "0" ; then
      $as_echo "yes" >&6;
      return 0
   else
      $as_echo "no" >&6;
      return 1
   fi
}
# Needed programs
AC_PROG_CC([gcc clang])
# On Xcode 5 gcc is an alias to clang
# We have to check some more things to know who this compiler really is
if test "$CC" = "gcc"; then
  check_gcc_is_aliased_to_clang "$CC"
  e=$?
  if test "$e" != "1"; then
    CC="clang"
  fi
fi
COMPILER=$CC
AC_PROG_CC_STDC()
AC_C_INLINE

#TODO wrap this to check whether the library is present
LDFLAGS="$LDFLAGS -lm" 

# this uses gcc, so it is necessary to have it before setting CFLAGS
AC_CHECK_LIB(gmp, __gmpz_init,
   [ AC_DEFINE([HAS_GMP], [1], [GMP installed])
     LDFLAGS="$LDFLAGS -lgmp" ],
   [ AC_CHECK_FILE(extern/gmp,
		   [],
		   [ AC_CONFIG_COMMANDS([extern-gmp],[ln -s gmp-local extern/gmp]) ])])

case "$COMPILER" in
     "gcc")
        CFLAGS=" -Wall -finline-limit=1000000 -Wno-unused-function"
        dnl CFLAGS=" -Wall -Wpadded -finline-limit=1000000 -Wno-unused-function"
     ;;
     "clang")
        CFLAGS=" -std=gnu89 -Wall -Wno-unused-function"
     ;;
     *)
     AC_MSG_ERROR("Unsupported compiler: $CC")
esac

AC_PROG_YACC
if test "$YFLAGS" = ""; then
   YFLAGS="-d"
fi

if test "x$ac_cv_prog_YACC" != "xbison -y"; then
   AC_MSG_ERROR("Cannot find Bison")
fi

AC_PROG_LEX

if test "x$ac_cv_prog_LEX" != "xflex"; then
   AC_MSG_ERROR("Cannot find Flex")
fi

# code syntactic checking
if test "$ARG_PEDANTIC" = "true"; then
   CFLAGS+=" -Wextra -pedantic -DPEDANTIC -Wconversion -Wdeclaration-after-statement -Wmissing-prototypes"
fi

# halt on all errors
if test "$ARG_STRICT" = "true"; then
   CFLAGS+=" -Werror"
fi

# optimization level
if test "$ARG_DEBUG" = "true"; then
   CFLAGS+=" -O0"
else
   CFLAGS+=" -O3 -DNDEBUG"
fi

# inlining and other debug stuff
if test "$ARG_DEBUG" = "true"; then
   CFLAGS+=" -Dinline=\"\" -ftrapv"
   CPPFLAGS+=" -DDEBUG"
   YFLAGS+=" --debug -v"
fi

# inlining and other debug_mem stuff
if test "$ARG_MEM" = "true"; then
   CFLAGS+=" -Dinline=\"\" -ftrapv"
   CPPFLAGS+=" -DMEM -DDEBUG"
fi

# source inside code
if test "$ARG_DEBUG" = "true" || test "$ARG_PROF" = "true" || test "$ARG_COVERAGE" = "true"; then
   CFLAGS+=" -g -g3 -gdwarf-2"
fi

# profiling output
if test "$ARG_PROF" = "true"; then
   CFLAGS+=" -pg"
else
   CFLAGS+=" -fomit-frame-pointer"
fi

# coverage
if test "$ARG_COVERAGE" = "true"; then
   CFLAGS+=" -fprofile-arcs -ftest-coverage"
fi

# static
if test "$ARG_STATIC" = "true"; then
   LDFLAGS+=" -static"
fi

AX_GCC_BUILTIN(__builtin_expect)
if $HAVE___BUILTIN_EXPECT; then
   CPPFLAGS="$CPPFLAGS -DHAVE___BUILTIN_EXPECT"
fi

AC_CHECK_PROGS(MAKE, $MAKE make gmake, error)

if test "x$MAKE" = "xerror"; then
   AC_MSG_ERROR("Cannot find GNU make command")
fi

AC_CHECK_PROGS(AR, ar, error)

if test "x$AR" = "xerror"; then
   AC_MSG_ERROR("Cannot find ar command")
fi

AC_CHECK_PROGS(DOXYGEN, doxygen, error)
AC_CHECK_PROGS(SPASS, spass, error)
AC_CHECK_PROGS(EPROVER, eprover, error)
AC_CHECK_PROGS(ETAGS, etags, error)
AC_CHECK_PROGS(CTAGS, ctags, error)

AC_SUBST(PROOF_PRODUCTION)
AC_SUBST(HAS_GMP)
AC_SUBST(CFLAGS)
AC_SUBST(LFLAGS)
AC_SUBST(YFLAGS)
AC_SUBST(CTAGS)
AC_SUBST(ETAGS)

AC_CONFIG_FILES([Makefile.config Makefile], [chmod a-w Makefile.config])

AC_OUTPUT()

AS_ECHO("")
AS_ECHO("")
AS_ECHO("Configuration summary")

AS_ECHO("CC = $CC")
AS_ECHO("CFLAGS = $CFLAGS")
AS_ECHO("CPPLAGS = $CPPFLAGS")
AS_ECHO("YFLAGS = $YFLAGS")
AS_ECHO("LFLAGS = $LFLAGS")
