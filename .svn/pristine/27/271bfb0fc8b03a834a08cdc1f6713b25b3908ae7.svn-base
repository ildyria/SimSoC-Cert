
FIG := generationStep
PNG := adc1

PS := $(FIG:%=%.ps) $(PNG:%=%.ps)
PDF := $(FIG:%=%.pdf)

FILES := $(PS) $(PDF)

.PRECIOUS: $(FILES)

default: main.pdf

%.pdf: %.tex $(PDF)
	pdflatex $<

%.ps: %.dvi
	dvips $<

%.dvi: %.tex $(PS)
	latex $<

%.ps: %.fig
	fig2ps --nogv $< > $@

%.pdf: %.fig
	fig2pdf --nogv $< > $@

%.ps: %.png
	pngtopnm $< |pnmtops> $@

clean:
	rm -f *~
	rm -f *.aux *.out *.log *.nav *.snm *.toc *.vrb
	rm -f $(FILES)
