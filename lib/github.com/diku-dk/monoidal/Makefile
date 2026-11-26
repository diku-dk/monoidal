FUTHARK ?= futhark
BACKEND ?=c
TEST_FLAGS ?=
REGRESSION_TESTS = $(wildcard test/*_regression.fut)

.PHONY: test
test:
	$(FUTHARK) test --backend=$(BACKEND) $(TEST_FLAGS) monoidal_ex.fut majority_ex.fut json_ex.fut $(REGRESSION_TESTS)

.PHONY: clean
clean:
	rm -rf *~ monoidal_ex majority_ex json_ex *.c *.actual *.expected *_regression
	rm -f test/*.c test/*.actual test/*.expected test/*_regression
