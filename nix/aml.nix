{
  lib,
  ocamlPackages,
}:
with ocamlPackages;
  buildDunePackage rec {
    pname = "aml";
    version = "dev";

    src = lib.cleanSource ../.;
  }
