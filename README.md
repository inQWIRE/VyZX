# VyZX

Verifying the ZX Calculus

[Check out the paper on arxiv](https://arxiv.org/abs/2205.05781)

## Building VyZX

Works with Coq 8.16-8.20.

First, install [QuantumLib](https://github.com/inQWIRE/QuantumLib) through opam.

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib
```

Then install [SQIR and VOQC](https://github.com/inQWIRE/SQIR)

```bash
opam pin -y coq-sqir https://github.com/inQWIRE/SQIR.git
opam pin -y coq-voqc https://github.com/inQWIRE/SQIR.git
```

Finally, build VyZX:

```bash
make
```

## Using the visualizer

To use the integrated visualization, two things will need to be installed and you must be using VSCode.

First, install [rocq-lsp](https://github.com/ejgallego/rocq-lsp) and install the associated VSCode extension.

Then install our VSCode extension, [ZXViz](https://marketplace.visualstudio.com/items?itemName=inQWIRE.vizx). It can also be built from source following the instructions [here](https://github.com/inQWIRE/ViZX/).

## Contributing

To contribute please make sure you use our validator hooks.
To configure the hooks run (you should only need to do this once):

```sh
make hooks
```
