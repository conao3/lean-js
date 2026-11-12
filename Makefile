# Run the targets inside the dev shell: `nix develop -c make check`.

.PHONY: install build pack gen-externs externs-check test test-public fuzz typecheck-generated embed-links embed-fixture status test-embed format format-check verify-links verify-fixture test-verify samples check

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
	vp lint $$(find test-out -name '*.ts' -not -path 'test-out/embed/*' -not -path 'test-out/project/*' -not -path 'test-out/verify/*')

# The fixture imports lean-ts and zod (its models are read by importing its modules).
embed-links: install
	mkdir -p test/embed/app/node_modules
	ln -sfn ../../../.. test/embed/app/node_modules/lean-ts
	ln -sfn ../../../../node_modules/zod test/embed/app/node_modules/zod

# Regenerate the committed modules of the embedding fixture.
embed-fixture: build pack embed-links
	node src/cli.ts sync --package test/embed/app --lean-typescript .lake/build/bin/lean-typescript

# The committed modules of the embedding fixture are fresh (no Lean).
status: pack embed-links verify-links
	node src/cli.ts status --package test/embed/app
	node src/cli.ts status --package test/verify/app

test-embed: build pack
	vp test test/embed.test.ts

verify-links: install
	mkdir -p test/verify/app/node_modules
	ln -sfn ../../../.. test/verify/app/node_modules/lean-ts
	ln -sfn ../../../../node_modules/zod test/verify/app/node_modules/zod

verify-fixture: build pack verify-links
	node src/cli.ts check --package test/verify/app --lean-typescript .lake/build/bin/lean-typescript

test-verify: build pack
	test/verify/test.sh

samples: build pack
	$(MAKE) -C samples verify test
	git diff --exit-code -- samples
	test -z "$$(git status --porcelain --untracked-files=all -- samples)"

format:
	treefmt

format-check: install
	treefmt --ci

check: format-check externs-check test test-public fuzz typecheck-generated status build pack verify-links test-verify samples
	vp run check
