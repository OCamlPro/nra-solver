{
  description = "NRA solver";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        ocamlPackages = pkgs.ocamlPackages;
      in
      {
        packages = rec {
          default = ocamlPackages.buildDunePackage {
            pname = "nra_solver";
            version = "dev";

            src = ./.;

            doCheck = true;

            buildInputs = [
              libpoly_bindings
            ] ++ (with ocamlPackages; [
              fmt
              logs
              zarith
              qcheck
              dolmen_loop
              cmdliner
              ctypes
              ctypes-foreign
            ]);
          };

          libpoly_bindings = ocamlPackages.buildDunePackage {
            pname = "libpoly_bindings";
            version = "dev";

            src = pkgs.fetchFromGitHub {
              owner = "Manelsadi";
              repo = "libpoly_ocaml_bindings";
              rev = "a06a7490b5f78b178d9a2a5c0f362bdf0f80dd8a";
              hash = "sha256-bwDNXN0Kl0UTQimK77JzpCUNRl9i5oo+cgQuiWDMxTc=";
            };

            propagatedBuildInputs = with pkgs; [ libpoly ];

            buildInputs = with ocamlPackages; [
              ctypes
              ctypes-foreign
              dune-configurator
              zarith
            ];
          };
        };

        formatter = pkgs.nixpkgs-fmt;

        checks.default = self.packages.${system}.default;

        devShells.default = pkgs.mkShell {
          packages = [ pkgs.gnumake ] ++ (with ocamlPackages; [
            utop
            odoc
            ocaml-lsp
            patdiff
          ]);

          inputsFrom = [ self.packages.${system}.default ];
        };
      });
}
