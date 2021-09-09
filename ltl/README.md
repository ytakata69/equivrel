Coq proofs on transformation between LTL and RA
===============================================

Formal proofs on a transformation between
an equation system on LTL with freeze quatifier and
a register automaton (RA).
The proofs were constructed using the [Coq](https://coq.inria.fr)
proof assistant.

- Pretty-printed definitions and statements of theorems are available
  in [automata.html](https://ytakata69.github.io/equivrel/automata.html),
  [raToEqnsys.html](https://ytakata69.github.io/equivrel/raToEqnsys.html),
  and other HTML files linked from them.
- To inspect the proofs, see the `.v` files in this repository.
  - `ltl.v`        - The definition of LTL formulas with freeze quantifier.
  - `eqnSys.v`     - The definition of equation systems on the LTL formulas.
  - `automata.v`   - The definition of the equation-system-to-RA transformation
                     and the proof of its correctness.
  - `raToEqnsys.v` - The definition of the RA-to-equation-system transformation
                     and the proof of its correctness.
