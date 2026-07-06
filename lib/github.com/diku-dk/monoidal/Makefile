FUTHARK ?= futhark
BACKEND ?=c

.PHONY: test
test:
	$(FUTHARK) test --backend=$(BACKEND) monoidal_ex.fut majority_ex.fut

.PHONY: clean
clean:
	rm -rf *~ monoidal_ex majority_ex *.c *.actual *.expected
