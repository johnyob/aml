{
  description = "Nix AML flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    treefmt = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    typix = {
      url = "github:loqusion/typix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    ocaml-overlay = {
      url = "github:nix-ocaml/nix-overlays";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs:
    with inputs;
      flake-utils.lib.eachDefaultSystem (
        system: let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              ocaml-overlay.overlays.default
              (import ./nix/overlay.nix)
            ];
          };
          typixLib = typix.lib.${system};
          typstLib = pkgs.callPackage ./nix/typst.nix {};

          fmt = treefmt.lib.evalModule pkgs {
            projectRootFile = "flake.nix";
            programs.alejandra.enable = true;
            programs.ocamlformat = {
              enable = true;
              package = pkgs.ocamlformat_0_26_2;
            };
            programs.typstyle.enable = true;
            settings.global.excludes = ["result" ".direnv" "_build"];
          };

          aml = pkgs.callPackage ./nix/aml.nix {};

          report = typixLib.buildTypstProject {
            src = pkgs.lib.sources.cleanSource ./report;
            fontPaths = with pkgs; [libertinus roboto];
            typstSource = "main.typ";
            TYPST_PACKAGE_CACHE_PATH = typstLib.typstPackagesCache [
              {
                name = "curryst";
                version = "0.3.0";
                sha256 = "sha256-TyA4XV57N1YDDVncy/sI06FWqAR+3mbqHisKmkRjqZE=";
              }
              {
                name = "ctheorems";
                version = "1.1.3";
                sha256 = "sha256-hzWgHWt88VLofnhaq4DB5JAGaWgt1rCDP4O9nknZzVY=";
              }
            ];
          };
        in {
          packages = {
            inherit aml report;
            default = report;
          };

          formatter = fmt.config.build.wrapper;
          devShells.default = typixLib.devShell {
            inputsFrom = [aml];
            fontPaths = with pkgs; [libertinus roboto];
            packages = with pkgs; [
              # Formatters
              alejandra
              ocamlformat_0_26_2

              # Typst
              typst
              tinymist
              typstyle

              # OCaml dev env
              ocamlPackages.utop
              ocamlPackages.ocaml-lsp
              ocamlPackages.merlin
              ocamlPackages.merlin-lib
              ocamlPackages.ocaml
              ocamlPackages.dune
            ];
          };
        }
      );
}
