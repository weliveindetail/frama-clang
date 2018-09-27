MAIN=main

C_CODE=$(wildcard examples/*.[ci])
VERSION_FILE=../../../../../VERSION
ifeq ("$(wildcard $(VERSION_FILE))", "")
VERSION_FILE=../../VERSION
FC_VERSION+=Chlorine+
else
#internal mode
FC_VERSION=$(shell cat $(VERSION_FILE))
endif
FCLANG_VERSION= $(shell cat $(VERSION_FILE))

DEPS_MODERN=fclangversion.tex biblio.bib macros.tex \
	introduction.tex \
	provides.tex \
	limitations.tex \
	changes.tex \
	$(C_CODE) \
	$(VERSION_FILE)

default: main.pdf

main.pdf: $(DEPS_MODERN)

EACSL_DIR=../..
DISTRIB_DIR=$(HOME)/frama-c/doc/www/distrib
install:
	mkdir -p $(EACSL_DIR)/doc/manuals/
	cp -f main.pdf $(EACSL_DIR)/doc/manuals/e-acsl-manual.pdf
#	cp -f main.pdf \
	  $(DISTRIB_DIR)/download/e-acsl/e-acsl-manual-$(EACSL_VERSION).pdf

include $(EACSL_DIR)/doc/support/MakeLaTeXModern

fclangversion.tex: Makefile
	rm -f $@
	printf '\\newcommand{\\fclangversion}{$(FCLANG_VERSION)\\xspace}\n' > $@
	printf '\\newcommand{\\fcversion}{$(FC_VERSION)\\xspace}\n' >> $@
	chmod a-w $@

%.1: %.mp
	mpost -interaction=batchmode $<

%.mps: %.1
	mv $< $@

%.pp: %.tex pp
	./pp -utf8 $< > $@

%.pp: %.c pp
	./pp -utf8 -c $< > $@

%.tex: %.ctex pp
	rm -f $@
	./pp $< > $@
	chmod a-w $@

%.bnf: %.tex transf
	rm -f $@
	./transf $< > $@
	chmod a-w $@

%_modern.bnf: %.tex transf
	rm -f $@
	./transf -modern $< > $@
	chmod a-w $@

%.ml: %.mll
	ocamllex $<

%.pdf: %.tex
	pdflatex $*
	makeindex $*
	bibtex $*
	pdflatex $*
	pdflatex $*

%.cmo: %.ml
	ocamlc -c $<

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

transfmain.cmo: transf.cmo

.PHONY: clean

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb* *.cm? *.bbl *.blg *.idx *.ind *.ilg \
		transf trans.ml pp.ml pp
	rm -f fclangversion.tex
