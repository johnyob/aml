{
  fetchurl,
  runCommand,
  lib,
  symlinkJoin,
  stdenvNoCC,
}: let
  typstPackageRegistry = "https://packages.typst.org";

  fetchTypstTarball = {
    namespace ? "preview",
    name,
    version,
    sha256,
  } @ args:
    fetchurl {
      url = "${typstPackageRegistry}/${namespace}/${name}-${version}.tar.gz";
      inherit sha256;
      downloadToTemp = true;

      # Build a reproducible tar, per instructions at https://reproducible-builds.org/docs/archives/
      postFetch = ''
        pushd $(mktemp -d)
        mkdir extracted
        tar -xzf $downloadedFile -C extracted
        tar --owner=0 --group=0 --numeric-owner --format=gnu \
                --sort=name --mtime="@1" \
                -czf extracted.tar.gz -C extracted .
        mv ./extracted.tar.gz $out
        popd
      '';
    };

  # Downloads a typst package from the package registry
  # Places the downloaded package to $out/${namespace}/${name}/${version}
  fetchTypstPackage = {
    namespace ? "preview",
    name,
    version,
    ...
  } @ args: let
    tarball = fetchTypstTarball args;
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
