# VyZX

Verifying the ZX Calculus

## Building VyZX

Works with Coq 8.16-8.18.

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

## Contributing

To contribute please make sure you use our validator hooks.
To configure the hooks run (you should only need to do this once):

```sh
make hooks
```
