scc = SimSoC-cert-compcert

TRANSFER = README errata.txt paperscript.v inv_le.v $(scc)-1.9.tgz $(scc)-1.11.tgz

all: tgz

.PHONY: www

www:
	cp -a $(TRANSFER) www/

tgz:
	rm -rf $(scc)-1.9-sauv $(scc)-1.11-sauv
	mv $(scc)-1.9 $(scc)-1.9-sauv
	mv $(scc)-1.11 $(scc)-1.11-sauv
	svn up
	tar czf $(scc)-1.9.tgz $(scc)-1.9
	tar czf $(scc)-1.11.tgz $(scc)-1.11
