TRANSFER = README paper.pdf paperscript.v simsoc-cert.tar.gz

all: ../cpp12.pdf simsoc-cert.tar.gz
	cp -a ../cpp12.pdf paper.pdf

.PHONY: www

www:
	cp -a $(TRANSFER) www/

simsoc-cert.tar.gz:
	tar czf $@ SimSoC-cert
