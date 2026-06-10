.PHONY: test
test:
	$(MAKE) -C lib/github.com/diku-dk/monoidal test

.PHONY: clean
clean:
	rm -rf *~
	$(MAKE) -C lib/github.com/diku-dk/monoidal clean
