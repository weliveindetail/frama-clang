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

### Main Makefile. As Makefiles included from clang and Frama-C are incompatible
### we have two auxiliary Makefiles, one for each side of the front-end.
### We define here general targets that will operate on both sides.

FCLANG_VERSION=0.0.10

PLUGIN_DIR ?= .
Frama_Clang_DIR ?= .

include $(PLUGIN_DIR)/Makefile.common

PLUGIN_NAME:=Frama_Clang
PLUGIN_ENABLED:=yes
PLUGIN_CMI:=intermediate_format
PLUGIN_CMO:=intermediate_format_parser frama_Clang_option		\
	    fclang_datatype reorder_defs cxx_utils mangling		\
	    convert_env convert_acsl generate_spec class convert	\
	    convert_link frama_Clang_register
ifneq ("$(MAKECMDGOALS)","uninstall")
PLUGIN_GENERATED:= \
 $(addprefix $(PLUGIN_DIR)/, \
  intermediate_format_parser.ml \
  intermediate_format.mli intermediate_format_parser.mli)
else
PLUGIN_GENERATED:=
endif
PLUGIN_DEPENDENCIES:= wp
ifeq ("$(RUN_TESTS)","yes")
PLUGIN_TESTS_DIRS:=basic stl class val_analysis template specs exn pp ppwp bugs da
else
PLUGIN_NO_TESTS:=yes
endif
PLUGIN_DISTRIBUTED:=no
PLUGIN_DISTRIB_EXTERNAL:=configure.ac configure Makefile Makefile.clang \
Makefile.common Makefile.config.in gen_ast.ml *.cpp *.h \
intermediate_format.ast DescentParse.template frama_Clang_config.ml.in \
Doxyfile mainpage.dox README.md \
$(addprefix share/libc++/,$(CXX_HEADERS))
include $(FRAMAC_SHARE)/Makefile.dynamic

$(Frama_Clang_DIR)/tests/ptests_config: $(Frama_Clang_DIR)/Makefile.config

install::
	$(MKDIR) $(FRAMAC_DATADIR)/frama-clang/libc++
	$(CP) $(addprefix $(Frama_Clang_DIR)/share/libc++/, \
                $(CXX_HEADERS)) \
              $(FRAMAC_DATADIR)/frama-clang/libc++

working-tests: $(Frama_Clang_DIR)/ptests_local_config.cmxs
	@echo "FRAMAC_SHARE=$(FRAMAC_SHARE)"
	LINES=$$(sed -e '/^Tests OK:$$/b out' -e d -e ':out' -e '=' -e 'd' \
                  $(Frama_Clang_DIR)/tests_list.txt); \
         TESTS=$$(tail -n +$$((LINES+1)) \
                       $(Frama_Clang_DIR)/tests_list.txt | tr '\n' ' '); \
         cd $(Frama_Clang_DIR) && $(PTESTS) $(PTESTS_OPTS) $$TESTS
	make -C $(Frama_Clang_DIR) 

tests:: dontrun

dontrun:
	(cd tests; echo `grep -r 'DONTRUN' $(PLUGIN_TESTS_DIRS) | wc -l` test files marked DONTRUN )

$(Frama_Clang_DIR)/gen_ast: $(Frama_Clang_DIR)/gen_ast.ml
	$(PRINT_OCAMLC) $@
	$(OCAMLC) $(Frama_Clang_BFLAGS) -o $@ -pp $(CAMLP5O) \
        /root/.opam/ocaml-base-compiler.4.08.1/lib/zarith/zarith.cma \
        dynlink.cma $^

$(Frama_Clang_DIR)/test_ast: \
  $(Frama_Clang_DIR)/intermediate_format.cmo \
  $(Frama_Clang_DIR)/intermediate_format.o

$(Frama_Clang_DIR)/%_parser.ml $(Frama_Clang_DIR)/%_parser.mli \
$(Frama_Clang_DIR)/%.mli $(Frama_Clang_DIR)/%.c: \
   $(Frama_Clang_DIR)/%.ast $(Frama_Clang_DIR)/gen_ast
	$(PRINT_MAKING) "intermediate AST"
	$(Frama_Clang_DIR)/gen_ast $<

CLANG_MAKE:=$(MAKE) PLUGIN_DIR=$(Frama_Clang_DIR) FRAMAC_SHARE=$(FRAMAC_SHARE) \
            -f $(Frama_Clang_DIR)/Makefile.clang SHELL='sh -x'

clean::
	$(RM) gen_ast
	$(CLANG_MAKE) clean

all::
	$(CLANG_MAKE) default

install::
	@echo "BINDIR is $(BINDIR)"
	$(CLANG_MAKE) install

doc::
	$(CLANG_MAKE) doc

distrib: clean
	$(PRINT_MAKING) $@
	$(RM) -r frama-clang
	$(MKDIR) frama-clang-$(FCLANG_VERSION)
	$(MKDIR) frama-clang-$(FCLANG_VERSION)/bin
	$(TAR) cf tmp.tar $(FCLANG_DISTRIBUTED_FILES)
	cd frama-clang-$(FCLANG_VERSION) && $(TAR) xf ../tmp.tar
	$(TAR) czf frama-clang-$(FCLANG_VERSION).tar.gz frama-clang-$(FCLANG_VERSION)
	$(RM) -r frama-clang-$(FCLANG_VERSION)

NOHEADER=$(addprefix $(Frama_Clang_DIR)/, configure README.md)

headers::
	$(PRINT_MAKING) $@
	headache -c $(Frama_Clang_DIR)/.headache_config.txt \
                 -h $(Frama_Clang_DIR)/.LICENSE \
                 $(filter-out $(NOHEADER), $(FCLANG_DISTRIBUTED_FILES))
