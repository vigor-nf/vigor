validator.byte: .PHONY
	corebuild -no-hygiene -use-menhir -lib dynlink -lib str \
	          validator.byte -use-ocamlfind -cflag -unsafe-string

.PHONY:

clean:
	rm -rf out
	rm -rf _build
	find -iname '*.cmo' -delete
	find -iname '*.cma' -delete
	find -iname '*.log' -delete
	rm -f validator.byte

vig%: clean validator.byte
	@if [ ! -e ../$@/klee-last ]; then \
	   printf '!!!\n\nPlease run symbex first.\n\n!!!\n'; exit 1; \
	 fi
	@cp ../$@/fspec.ml $@_fspec.ml
	@corebuild -no-hygiene -lib dynlink -lib str \
	           common_fspec.cmo $@_fspec.cmo -cflag -unsafe-string
	@ocamlc -a _build/common_fspec.cmo _build/$@_fspec.cmo -o $@_fspec.cma
	@python3 translate-spec.py ../$@/$(or $(VIGOR_SPEC),spec.py) \
	         forwarding_property.tmpl ../$@
	@/usr/bin/time -v ./test_all.sh ../$@/klee-last out .. $@_fspec.cma $@

# Regression test suite
#test-results/%.done: regression-tests/%
#	./run-test.sh $* test-results
#	touch $@
#check: $(patsubst regression-tests/%,test-results/%.done,$(wildcard regression-tests/*))
