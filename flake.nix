{
  description = "lean-ts: a Lean IR -> TypeScript backend with a typed runtime";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ inputs.treefmt-nix.flakeModule ];

      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      perSystem =
        { pkgs, config, ... }:
        let
          nodejs = pkgs.nodejs_26;
          pnpm = pkgs.pnpm.override { nodejs-slim = pkgs.nodejs-slim_26; };

          vp = pkgs.writeShellApplication {
            name = "vp";
            runtimeInputs = [
              nodejs
              pnpm
            ];
            text = ''
              workspace_root="$PWD"
              while [[ "$workspace_root" != / && ! -f "$workspace_root/pnpm-workspace.yaml" ]]; do
                workspace_root="$(dirname "$workspace_root")"
              done

              if [[ ! -f "$workspace_root/pnpm-workspace.yaml" ]]; then
                printf '%s\n' "vp must run inside the lean-ts workspace" >&2
                exit 1
              fi

              if [[ "''${1:-}" == install ]]; then
                shift
                exec pnpm install "$@"
              fi

              vp_cli="$workspace_root/node_modules/vite-plus/bin/vp"
              if [[ ! -f "$vp_cli" ]]; then
                printf '%s\n' "The local Vite+ CLI is missing; run 'vp install' first" >&2
                exit 1
              fi

              export PATH="${nodejs}/bin:$workspace_root/node_modules/.bin:$PATH"
              exec ${nodejs}/bin/node "$vp_cli" "$@"
            '';
          };
        in
        {
          packages.lean-typescript = pkgs.stdenv.mkDerivation {
            pname = "lean-typescript";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./lakefile.toml
                ./lean-toolchain
                ./Main.lean
                ./LeanTs.lean
                ./LeanTs
              ];
            };
            nativeBuildInputs = [
              pkgs.lean4
              pkgs.makeWrapper
            ];
            buildPhase = ''
              export HOME=$TMPDIR
              lake build lean-typescript
            '';
            installPhase = ''
              install -Dm755 .lake/build/bin/lean-typescript $out/bin/lean-typescript
              wrapProgram $out/bin/lean-typescript --set-default LEAN_SYSROOT ${pkgs.lean4}
            '';
            meta.mainProgram = "lean-typescript";
          };

          packages.default = config.packages.lean-typescript;

          treefmt = {
            projectRootFile = "flake.nix";
            programs.nixfmt.enable = true;
            settings.formatter.oxfmt = {
              command = "${vp}/bin/vp";
              options = [ "fmt" ];
              includes = [
                "*.ts"
                "*.mjs"
                "*.json"
                "*.yaml"
                "*.yml"
              ];
              excludes = [ "lake-manifest.json" ];
            };
          };

          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.lean4
              nodejs
              pnpm
              vp
              pkgs.gcc
              config.treefmt.build.wrapper
            ];
          };
        };
    };
}
