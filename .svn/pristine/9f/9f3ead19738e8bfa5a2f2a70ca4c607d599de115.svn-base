BUILD=$(PWD)
SRC=$(PWD)
FIG=$(SRC)/fig
NAME=abstract

TEXINPUTS=.:$(SRC):$(SRC)/sty:$(SRC)/pdf:$(FIG)::

FIGURESBASE=${shell grep -h '\\insertfig' $(SRC)/*.tex |  perl -pe 's/^.*\\insertfig\{([a-zA-Z0-9_-]*)\}.*$$/\1.fig/'}
FIGUREPS=$(FIGURESBASE:%.fig=$(BUILD)/%.pstex)
FIGUREPDFTEX=$(FIGURESBASE:%.fig=$(BUILD)/%.pdftex_t)
FIGUREPDF=$(FIGURESBASE:%.fig=$(BUILD)/%.pdf)
FIGUREOBJS=$(FIGUREPS) $(FIGUREPDFTEX) $(FIGUREPDF)

FIG2PDFTEX=fig2dev -L pdftex_t -p $(BUILD)/$*.pdf $< $@
FIG2PS=fig2dev -L pstex $< $(BUILD)/$*.pstex
FIG2PDF=epstopdf $(BUILD)/$*.pstex -o $(BUILD)/$*.pdf
# JF -> Claude : pstopdf obsoleted by epstopdf


all: $(BUILD)/$(NAME).pdf

clean:
	rm -f *~ $(FIGUREOBJS) $(NAME).aux $(NAME).blg $(NAME).bbl $(NAME).log

cleanall: clean
	rm -f $(NAME).pdf

$(BUILD)/%.pdftex_t: $(FIG)/%.fig
	$(FIG2PDFTEX)

$(BUILD)/%.pstex: $(FIG)/%.fig
	$(FIG2PS)
	$(FIG2PDF)

# fake
$(BUILD)/%.pdf: %.pstex
	$(FIG2PDF)

$(BUILD)/$(NAME).pdf: force $(FIGUREOBJS)
	cd $(BUILD) && \
	TEXINPUTS=$(TEXINPUTS); export TEXINPUTS; \
	pdflatex --interaction nonstopmode $(SRC)/$(NAME)

bib: force
	cd $(BUILD) && \
	cp $(SRC)/$(NAME).bib $(BUILD) && \
	TEXINPUTS=$(TEXINPUTS); export TEXINPUTS; \
	bibtex $(BUILD)/$(NAME)

force:

