# VyZX
Verifying the ZX Calculus

[Check out the paper on arxiv](https://arxiv.org/abs/2205.05781)

## Building VyZX

Tested with Coq 8.15.2.

First install [QuantumLib](https://github.com/inQWIRE/QuantumLib) through opam.

Then run
```
coq_makefile -f _CoqProject -o Makefile
make
```


## Contributing

To contribute please make sure you use our validator hooks.
To configure the hooks run
```sh
make hooks
```