(lang dune 2.8)
(name coq-vyzx)
(version 0.1.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
(source (github inQWIRE/VyZX))

(package
 (name coq-vyzx)
 (synopsis "Coq library for reasoning about ZX diagrams")
 (description "\| inQWIRE's QuantumLib is a Coq library for reasoning
              "\|  about ZX diagrams.
 )

 (depends
   (coq-quantumlib (>= 1.5.0))
   (coq-sqir (>= 1.3.0))
   (coq-voqc (>= 1.3.0))
   (coq (>= 8.16))))
