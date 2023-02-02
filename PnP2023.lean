import PnP2023.Lec_01_04.Intro
import PnP2023.Lec_01_04.OddExample
import PnP2023.Lec_01_06.NatEq
import PnP2023.Lec_01_11.NatLe
import PnP2023.Lec_01_13.NatRec
import PnP2023.Lec_01_18.NatSub
import PnP2023.Lec_01_20.NatMin
import PnP2023.Lec_01_20.NatMinus
import PnP2023.Lec_01_25.Answer
import PnP2023.Lec_02_01.Foundations
/-!
# Proofs and Programs 2023

This course will introduce [Lean Theorem Prover 4](https://leanprover.github.io/), which is an _interactive theorem prover_ as well as a programming language and use it for various aspects of _proofs and programs_:

* Using programs (_interactive theorem provers_) to
    * verify proofs of results
    * help in generating proofs
* Proving correctness of programs
* Writing programs to find and/or verify proofs
* _Functional Programming_ in Lean

To study these things in a meaningful way, we will look at _foundations_ of _mathematics_ and of _computation_. We will introduce different foundational systems:

* _Dependent Type Theory_ (DTT): foundations used by Lean that include both proofs and computations in a unified way.
* Classical foundations:
  - _First-order logic:_ the usual foundations of mathematics.
  - _lambda-calculus:_ one of the equivalent formulations of the usual foundations of computation.

## Navigation

To browse the code, expand the `PnP2023` tab on the left.

-/

def hello := "to the course Proofs and Programs"
