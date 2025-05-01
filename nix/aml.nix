{
  lib,
  ocamlPackages,
}:
with ocamlPackages;
  buildDunePackage rec {
    pname = "aml";
    version = "dev";

    src = lib.cleanSource ../.;

    nativeBuildInputs = [
      menhir
    ];

    propagatedBuildInputs = [
      core
      core_unix
      ppx_jane
      grace
      menhir
      fmt
    ];
  }
