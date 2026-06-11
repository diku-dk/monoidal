FUTHARK ?= futhark

.PHONY: test
test:
	$(FUTHARK) test monoidal_ex.fut majority_ex.fut

.PHONY: clean
clean:
	rm -rf *~ monoidal_ex majority_ex *.c
