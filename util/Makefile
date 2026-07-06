# Makefile for constructing random strings for processing by the monoidal library

MLCOMP ?= mlkit

.PHONY: all
all: ex50.txt ex100.txt ex200.txt ex400.txt ex800.txt ex1600.txt ex3200.txt ex6400.txt ex12800.txt

lib:
	smlpkg sync

gen.exe: gen.mlb gen.sml lib
	$(MLCOMP) -o $@ $<

ex%.txt: gen.exe
	./$< -N $* > $@

.PHONY: clean
clean:
	rm -rf *~ MLB gen.exe *.txt

.PHONY: realclean
realclean:
	$(MAKE) clean
	rm -rf lib
