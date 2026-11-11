# Run the targets inside the dev shell: `nix develop -c make check`.

.PHONY: install build pack gen-externs externs-check test test-public fuzz typecheck-generated embed-fixture status test-embed format format-check check

install:
	pnpm install --frozen-lockfile

build: install
	lake build lean-typescript LeanTsTest

pack: install
	vp pack

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
	vp lint $$(find test-out -name '*.ts' -not -path 'test-out/embed/*' -not -path 'test-out/project/*')

# Regenerate the committed modules of the embedding fixture.
embed-fixture: build pack
	node src/cli.ts sync --package test/embed/app --lean-typescript .lake/build/bin/lean-typescript

# The committed modules of the embedding fixture are fresh (no Lean).
status: install
	node src/cli.ts status --package test/embed/app

test-embed: build pack
	vp test test/embed.test.ts

format:
	treefmt

format-check: install
	treefmt --ci

check: format-check externs-check test test-public fuzz typecheck-generated status build pack
	vp run check
