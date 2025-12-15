
This directory contains the Why3 proofs for the paper "When Separation
Arithmetic is Enough" (see https://usr.lmf.cnrs.fr/~jcf/sep-arith/ )

To replay the proofs:

- install
  * Why3 1.8.0  https://www.why3.org/
  * Alt-Ergo 2.6.0 https://alt-ergo.ocamlpro.com/
  * Z3 4.14.1 https://github.com/z3prover/z3/releases
  * CVC5 1.1.2 https://github.com/cvc5/cvc5/releases
  * CVC4 1.8 https://cvc4.github.io/2020/06/19/cvc4-1.8-released.html

- run
  ```
    why3 config detect
  ```

- run
  ```
  why3 replay reversal
  why3 replay morris
  ```

If everything goes as expected, the output should be as follows:
  ```
  11/11 (replay OK)
  19/19 (replay OK)
  ```
