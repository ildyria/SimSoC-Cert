# Only for making auxiliary .tex files from $(COQMAIN).v and $(MAIN).tex
# which are the only source file
# $HeadURL: https://scm.gforge.inria.fr/anonscm/svn/simsoc-cert/papers/itp13/Makefile $
# $LastChangedDate: 2013-04-17 11:27:16 +0200 (Wed, 17 Apr 2013) $
# $LastChangedRevision: 2297 $
# $LastChangedBy: monin $

# Use: make dep1; make dep2; make

# If you insist on compiling the main tex files: make pdf

MAIN=itp13.tex
TARG=$(MAIN:.tex=.pdf)
COQMAIN=coq.v

# generates $(TEXSRC) and $(COQCHUNKS)
MKDEP1=MakefileSRC.dep
MKDEP2=MakefileCOQCHUNKS.dep

COQDOC=coqdoc --latex --body-only 

sinclude $(MKDEP1)
sinclude $(MKDEP2)

INCLCOQTEX=${patsubst %,%.tex,${COQCHUNKS}}


all: $(INCLCOQTEX) submission

submission:
	./mksubmission

pdf: $(TARG)

$(TARG): $(MAIN) $(INCLCOQTEX)
	pdflatex $(MAIN)
	bibtex $(MAIN:.tex=)
	pdflatex $(MAIN)
	pdflatex $(MAIN)

$(INCLCOQTEX): coq.tex
	cat $< | sed -n -e '/begin $(@:.tex=)/,/end $(@:.tex=)/p' | \
	         sed -e 's/begin $(@:.tex=) //' | \
	         sed -e '/$(@:.tex=)/d' | \
	         sed -e 's/coqdoctac{eval}/coqdocvar{eval}/g' | \
        cat > $@

test:
	echo TEXSRC = $(TEXSRC)
	echo COQCHUNKS = $(COQCHUNKS)
	echo INCLCOQTEX=$ = $(INCLCOQTEX)

coq.tex: $(COQMAIN)
	$(COQDOC) $<

dep1: 
	echo 'TEXSRC=$(MAIN) \\' > $(MKDEP1)
	egrep '^\\input' itp13.tex | \
	    sed -e 's/.input./\t/' -e 's/}.*/.tex \\/' \
	    >> $(MKDEP1)
	echo '	'>> $(MKDEP1)

dep2: 
	rm -f chunk*.tex
	echo 'COQCHUNKS= \\' > $(MKDEP2)
	cat $(TEXSRC) | egrep '^\\coqdocinput'  | \
	    sed -e 's/.coqdocinput./\t/' -e 's/}.*/ \\/' \
	    >> $(MKDEP2)
	echo '	'>> $(MKDEP2)

clean:
	rm $(MKDEP1) $(MKDEP2) $(INCLCOQTEX)
