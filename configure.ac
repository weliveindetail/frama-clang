##########################################################################
#                                                                        #
#  This file is part of Frama-Clang                                      #
#                                                                        #
#  Copyright (C) 2012-2020                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file LICENSE).                      #
#                                                                        #
##########################################################################

m4_define([plugin_file],Makefile.config.in)

m4_define([FRAMAC_SHARE_ENV],
          [m4_normalize(m4_esyscmd([echo $FRAMAC_SHARE]))])

m4_define([FRAMAC_SHARE],
          [m4_ifval(FRAMAC_SHARE_ENV,
                    [FRAMAC_SHARE_ENV],
                    [m4_esyscmd(frama-c -print-path)])])

m4_ifndef([FRAMAC_M4_MACROS],
          [m4_include(FRAMAC_SHARE/configure.ac)])

check_plugin([frama_clang],PLUGIN_RELATIVE_PATH(plugin_file),
             [C++ front-end for Frama-C],yes)

plugin_require_external(frama_clang,camlp5o)
plugin_use(frama_clang,wp)

# check for system C++ compiler, as we can't rely on clang++ itself because
# of potential incompatibilities with GNU libstdc++ v5.
# See https://llvm.org/bugs/show_bug.cgi?id=23529 for more details
AC_PROG_CXX()

configure_tool([CAMLP5O],[camlp5o],[camlp5o not found.],no)
check_plugin_dependencies()

AC_SUBST(CLANG_CXXFLAGS)
AC_SUBST(CLANG_CFLAGS)
AC_SUBST(CLANG_INCDIR)
AC_SUBST(CLANG_LINKFLAGS)
AC_SUBST(CLANG_SYSLIBS)
AC_SUBST(CLANG_BIN_DIR)
AC_SUBST(LLVM_LIBS)
AC_SUBST(LLVM_VERSION)
AC_SUBST(DEFAULT_FC_C_HEADERS)
AC_SUBST(DEFAULT_FC_CXX_HEADERS)
AC_SUBST(RUN_TESTS)

DEFAULT_FC_C_HEADERS=$datarootdir/frama-c/libc
DEFAULT_FC_CXX_HEADERS=$datarootdir/libc++

AC_CHECK_PROGS([CLANG],[clang clang-11 clang-10 clang-9 clang-8 clang-7 clang-6.0],no)
AC_CHECK_PROGS([CLANGXX],[clang++ clang++-11 clang++-10 clang++-9 clang++-8 clang++-7 clang++6.0],no)
AC_CHECK_PROGS([LLVM_CONFIG],[llvm-config llvm-config-11 llvm-config-10 llvm-config-9 llvm-config-8 llvm-config-7 llvm-config-6.0],no)

if test "$LLVM_CONFIG" = "no"; then
  plugin_disable(frama_clang,[llvm-config not found]);
fi
if test "$CLANG" = "no"; then
  plugin_disable(frama_clang,[clang not found]);
fi
if test "$CLANG++" = "no"; then
  plugin_disable(frama_clang,[clang++ not found]);
fi

if test "$ENABLE_FRAMA_CLANG" != "no"; then

LLVM_VERSION=$($LLVM_CONFIG --version)

AC_MSG_CHECKING([LLVM version])

LLVM_SHARED_MODE=$($LLVM_CONFIG --shared-mode)

RUN_TESTS=no

case $LLVM_VERSION in
  6.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]);;
  7.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]);;
  8.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]);;
  9.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]); RUN_TESTS=yes;;
  10.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]); RUN_TESTS=yes;;
  11.0.*) AC_MSG_RESULT([$LLVM_VERSION: Good]);;
  *) plugin_disable(frama_clang,
      [[LLVM Version $LLVM_VERSION is not supported. Please install LLVM 6.0.x, 7.0.x, 8.0.x, 9.0.x, or 10.0.x]]);;
esac

LLVM_CONFIG="$LLVM_CONFIG $LLVM_STATIC"

CLANG_CXX_COMMONFLAGS="$($LLVM_CONFIG --cppflags) -fPIC"
CLANG_CFLAGS="$($LLVM_CONFIG --cppflags) -fPIC"
CLANG_INCDIR=$($LLVM_CONFIG --includedir)
CLANG_LINKFLAGS="$($LLVM_CONFIG --ldflags)"
CLANG_CXXFLAGS="$($LLVM_CONFIG --cxxflags) -fPIC"
CLANG_SYSLIBS="$($LLVM_CONFIG --system-libs)"
CLANG_BIN_DIR="$($LLVM_CONFIG --bindir)"
if test "$LLVM_SHARED_MODE" = "shared"; then
LLVM_LIBS=$($LLVM_CONFIG --libs core);
else
LLVM_LIBS=$($LLVM_CONFIG --libs profiledata asmparser mc mcparser support bitreader option);
fi
fi

write_plugin_config(Makefile.config)
