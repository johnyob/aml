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

          fmt = treefmt.lib.evalModule pkgs {
            projectRootFile = "flake.nix";
            programs.alejandra.enable = true;

            settings.global.excludes = ["result" ".direnv"];
          };

          report = typixLib.buildTypstProject {
            src = typixLib.cleanTypstSource ./.;
            typstSource = "main.typ";
          };

        in {
          packages = {
            inherit report;
            default = report;
          };

          formatter = fmt.config.build.wrapper;
          devShells.default = typixLib.devShell {
            fontPaths = with pkgs; [ libertinus roboto ];
            packages = with pkgs; [
              alejandra lefthook typstyle
            ];
          };
        }
      );
}
