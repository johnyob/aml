final: prev:
with prev; {
  ocamlPackages = final.ocaml-ng.ocamlPackages_5_2;

  ocaml-ng =
    ocaml-ng
    // (with ocaml-ng; {
      ocamlPackages_5_2 = ocamlPackages_5_2.overrideScope (
        _: prev:
          with prev; {
            # ocaml-overlay is broken for unsable nixpkgs
            # TODO: upstream patch for ocaml-overlay logs pkg
            logs = prev.logs.overrideAttrs (_: {
              buildPhase = "${topkg.run} build --with-lwt true --with-cmdliner true --with-fmt true --with-js_of_ocaml false";
            });
          }
      );
    });
}
