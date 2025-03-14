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
  };

  outputs = inputs:
    with inputs;
      flake-utils.lib.eachDefaultSystem (
        system: let
          pkgs = import nixpkgs {
            inherit system;
          };
          typixLib = typix.lib.${system};
          typstLib = pkgs.callPackage ./nix/typst.nix {};

          fmt = treefmt.lib.evalModule pkgs {
            projectRootFile = "flake.nix";
            programs.alejandra.enable = true;
            settings.global.excludes = ["result" ".direnv"];
          };

          report = typixLib.buildTypstProject {
            src = pkgs.lib.sources.cleanSource ./.;
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
            inherit report;
            default = report;
          };

          formatter = fmt.config.build.wrapper;
          devShells.default = typixLib.devShell {
            fontPaths = with pkgs; [libertinus roboto];
            packages = with pkgs; [
              alejandra
              lefthook
              typstyle
            ];
          };
        }
      );
}
