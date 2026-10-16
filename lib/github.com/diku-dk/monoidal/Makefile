FUTHARK ?= futhark
BACKEND ?=c

.PHONY: test
test:
	$(FUTHARK) test --backend=$(BACKEND) monoidal_ex.fut majority_ex.fut parens_regression.fut parens_hom_regression.fut decimal_regression.fut nested_numeric_regression.fut parens_tuple*_regression.fut

.PHONY: clean
clean:
	rm -rf *~ monoidal_ex majority_ex *.c *.actual *.expected *_regression
