# Run the targets inside the dev shell: `nix develop -c make check`.

.PHONY: install build gen-externs externs-check test test-public fuzz typecheck-generated format format-check check

install:
	pnpm install --frozen-lockfile

build: install
	lake build lean-typescript LeanTsTest

gen-externs: install
	node scripts/gen-externs.ts > LeanTs/RuntimeExterns.lean.tmp
	mv LeanTs/RuntimeExterns.lean.tmp LeanTs/RuntimeExterns.lean

# The committed extern list must match the runtime.
externs-check: gen-externs
	git diff --exit-code -- LeanTs/RuntimeExterns.lean

test: build
	./test-diff.sh

fuzz: build
	./fuzz.sh

test-public: build
	./test-public.sh

# Type-check and lint every module the diff-test generated (test-out/ is gitignored, so it is passed explicitly).
typecheck-generated: test test-public fuzz
	vp lint $$(find test-out -name '*.ts')

format:
	treefmt

format-check: install
	treefmt --ci

check: format-check externs-check test test-public fuzz typecheck-generated
	vp run check
