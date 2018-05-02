SRC=$(PWD)
FIG=$(SRC)/fig
NAME=cpp

TEXINPUTS=.:$(SRC):$(SRC)/sty:$(SRC)/LaTeX-template:$(SRC)/pdf:$(FIG)::

FIGURESBASE=$(shell cd $(FIG) && ls *fig)
FIGUREPDF=$(FIGURESBASE:%.fig=$(FIG)/%.pdf)
FIGUREOBJS=$(FIGUREPDF)

FIG2PDFTEX=fig2dev -L pdftex_t -p $*.pdf $< $@
FIG2PS=fig2dev -L pstex $< $*.pstex
FIG2PDF=fig2mpdf $< 
# FIG2PDF=fig2mpdf $< && mv $*.pdf $(FIG)
# JF -> Claude : pstopdf obsoleted by epstopdf


all: $(NAME).pdf

clean:
	rm -f *~ $(FIGUREOBJS) $(NAME).aux $(NAME).blg $(NAME).bbl $(NAME).log

cleanall: clean
	rm -f $(NAME).pdf

# fake
$(FIG)/%.pdf: $(FIG)/%.fig
	$(FIG2PDF)

$(NAME).pdf: force $(FIGUREOBJS)
	TEXINPUTS=$(TEXINPUTS); export TEXINPUTS; \
	pdflatex --interaction nonstopmode $(SRC)/$(NAME)

bib: force
	TEXINPUTS=$(TEXINPUTS); export TEXINPUTS; \
	bibtex $(NAME)

force:

