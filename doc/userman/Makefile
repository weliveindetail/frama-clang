MAIN=main

C_CODE=$(wildcard examples/*.[ci])
FC_VERSION+=Potassium+

DEPS_MODERN=biblio.bib \
	changes.tex \
    description.tex \
	grammar.tex \
	introduction.tex \
	limitations.tex \
	macros.tex \
	preprocessing.tex \
	fclangversion.tex \
	$(C_CODE) \
	Makefile

default: main.pdf

main.pdf: main.tex $(DEPS_MODERN)

FCLANG_DIR=../..
DISTRIB_DIR=$(HOME)/frama-c/doc/www/distrib
install:
	mkdir -p $(FCLANG_DIR)/doc/manuals/
	cp -f main.pdf $(FCLANG_DIR)/doc/manuals/fclang-manual.pdf

include $(FCLANG_DIR)/doc/support/MakeLaTeXModern

version.tex: Makefile

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
