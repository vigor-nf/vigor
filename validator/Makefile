# allow the use of extglob in paths
SHELL = /bin/bash -O extglob -c

all: validator.byte nat_fspec.cma bridge_fspec.cma balancer_fspec.cma policer_fspec.cma fw_fspec.cma

validator.byte: .PHONY
	corebuild -no-hygiene -use-menhir -lib dynlink -lib str validator.byte -use-ocamlfind -cflag -unsafe-string

%.cma: _build/common_fspec.cmo _build/%.cmo
	ocamlc -a $^ -o $@

_build/%.cmo: .PHONY
	corebuild -no-hygiene -lib dynlink -lib str $(notdir $@) common_fspec.ml -cflag -unsafe-string

.PHONY:

clean:
	rm -rf out
	rm -rf _build
	find -iname '*.cmo' -delete
	find -iname '*.cma' -delete
	find -iname '*.log' -delete
	rm -f validator.byte

validate-nat: clean
	$(eval SPEC ?= nat-spec.py)
	python3 translate-spec.py $(SPEC) forwarding_property.tmpl
	./test_all.sh ../nf/vignat/klee-last out ../nf nat_fspec.cma

validate-bridge: clean
	$(eval SPEC ?= bridge-spec.py)
	python3 translate-spec.py $(SPEC) bridge_forwarding_property.tmpl
	./test_all.sh ../nf/vigbridge/klee-last out ../nf bridge_fspec.cma

validate-balancer: clean
	$(eval SPEC ?= lb-spec.py)
	python3 translate-spec.py $(SPEC) balancer_forwarding_property.tmpl
	./test_all.sh ../nf/vigbalancer/klee-last out ../nf balancer_fspec.cma

validate-policer: clean
	$(eval SPEC ?= policer-spec.py)
	python3 translate-spec.py $(SPEC) policer_forwarding_property.tmpl
	./test_all.sh ../nf/vigpolicer/klee-last out ../nf policer_fspec.cma

validate-fw: clean
	$(eval SPEC ?= fw-spec.py)
	python3 translate-spec.py $(SPEC) fw_forwarding_property.tmpl
	./test_all.sh ../nf/vigfw/klee-last out ../nf fw_fspec.cma

# Regression test suite
test-results/%.done: regression-tests/%
	./run-test.sh $* test-results
	touch $@

check: $(patsubst regression-tests/%,test-results/%.done,$(wildcard regression-tests/*))

loc-spec:
	cloc --by-file !(translate-spec).py
