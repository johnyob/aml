# AML
> An ML with ambivalent types and type-level equalities

AML is a work-in-progress specification for the inference of ambivalent types 
in OCaml. It builds on Garrigue and Rémy's[^1] system but uses a radically different
presentation.

## Getting Started

> [!NOTE]
> AML is built with Nix, a package manager and system configuration tool that makes building from sources easy! See the [Nix docs](https://nixos.org/download/) for instructions for your system. Additionally, ensure [Nix flakes are enabled](https://nixos.wiki/wiki/Flakes#Enable_flakes).


To build AML from source, follow these steps:
```sh
# Clone the repository
❯ git clone https://github.com/johnyob/aml.git && cd aml
# Enter the Nix development environment
❯ nix develop
# Build 🚀
❯ make 
```

We strongly recommend using Nix. Nevertheless, AML can be built using `typst` directly. 
See the [Typst docs](https://github.com/typst/typst?tab=readme-ov-file#installation) for instructions 
for your system. After installing `typst`, simply run:
```sh
❯ make
``` 

## Quick Start


> [!TIP]
> Use [Tinymist](https://github.com/Myriad-Dreamin/tinymist), an integrated language server for Typst. See the [Tinymist Docs](https://github.com/Myriad-Dreamin/tinymist?tab=readme-ov-file#installation) for instructions for your editor.

To get started with writing / modifying the AML specification, run the command below:
```sh
❯ make watch
```



[^1]: Jacques Garrigue, Didier Rémy. Ambivalent Types for Principal Type Inference with GADTs (extended version). 2013. [⟨hal-00914493v2⟩](https://inria.hal.science/hal-00914493v2)