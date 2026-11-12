LEAN_TYPESCRIPT ?= $(abspath ../.lake/build/bin/lean-typescript)
export LEAN_TYPESCRIPT

SAMPLES := word-count roman-numerals todo-cli sorted-search inventory generic-search pricing-api verified-typescript
STEPS := $(sort $(wildcard steps/*/))
VERIFY := verified-typescript sorted-search inventory steps/10-ensures steps/11-requires steps/12-refines steps/13-loops steps/14-schemas

.PHONY: test verify

test:
	for s in $(STEPS) $(SAMPLES); do ./run.sh $$s || exit 1; done

verify:
	for s in $(VERIFY); do (cd $$s && node node_modules/lean-ts/dist/cli.js check --package . --require proved) || exit 1; done
