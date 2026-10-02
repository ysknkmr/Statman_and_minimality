# Direct check of the order-4 axiom S(G')

Self-contained Lean 4 development (core library only; no Mathlib, no `sorry`,
no `native_decide`), independent of `../lean/`.

For the formula S(G') displayed in Corollary `cor:LC`, it proves

* `IL_SG_eq_LC : ∀ φ, Thm [SG] φ ↔ Thm [LCax] φ`  (IL ⊕ S(G') = LC),
* `SG_minimal  : MinimalCL SG`                    (S(G') is minimal in CL),
* `SG_ord      : ord SG = 4`.

## What to read

* `SGprime/Defs.lean`: all definitions used in the statements (imports nothing).
* `SGprime/Main.lean`: the three statements, each proved by citing a lemma of
  `Lemmas.lean` with exactly the same statement.

`SGprime/Lemmas.lean` contains the routine and computational lemmas and need
not be read.  It defines no notation, so the statements in `Main.lean` mean
what they say in terms of `Defs.lean`.

## Checking

    lake build

This takes about 10 seconds and prints the axioms used by the three theorems
(at most `propext`, `Quot.sound`, `Classical.choice`).
