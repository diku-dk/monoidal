.PHONY: test
test:
	$(MAKE) -C lib/github.com/diku-dk/monoidal test

.PHONY: clean
clean:
	rm -rf *~
	$(MAKE) -C lib/github.com/diku-dk/monoidal clean
	$(MAKE) -C util clean

doc:
	futhark doc -o doc lib/github.com/diku-dk/monoidal

.PHONY: realclean
realclean:
	$(MAKE) clean
	rm -rf doc
