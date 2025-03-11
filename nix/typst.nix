{
  fetchurl,
  runCommand,
  lib,
  symlinkJoin,
  stdenvNoCC,
}: let
  typstPackageRegistry = "https://packages.typst.org";

  # Downloads a typst package from the package registry
  # Places the downloaded package to $out/${namespace}/${name}/${version}
  fetchTypstPackage = {
    namespace ? "preview",
    name,
    version,
    sha256,
  }: let
    tarball = fetchurl {
      url = "${typstPackageRegistry}/${namespace}/${name}-${version}.tar.gz";
      inherit sha256;
    };

    packageSubdir = "${namespace}/${name}/${version}";
  in
    runCommand "fetch-typst-package-${namespace}-${name}-${version}" {} ''
      tarball=${tarball}
      mkdir -p $out/${packageSubdir}
      tar -xzf $tarball -C $out/${packageSubdir}
    '';
in {
  typstPackagesCache = packageSpecs: let
    typstPackages = lib.lists.forEach packageSpecs fetchTypstPackage;
  in
    symlinkJoin {
      name = "typst-packages-src";
      paths = typstPackages;
    };
}
