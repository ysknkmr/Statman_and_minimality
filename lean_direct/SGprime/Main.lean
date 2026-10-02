import SGprime.Lemmas

/-!
# Main theorems

Together with `SGprime/Defs.lean`, this is the only file a reader needs to
read.  The statements below use only the definitions of `Defs.lean`:

* `IL_SG_eq_LC : ∀ φ, Thm [SG] φ ↔ Thm [LCax] φ`  (`IL ⊕ S(G') = LC`),
* `SG_minimal  : MinimalCL SG`                    (`S(G')` is `CL`-minimal),
* `SG_ord      : ord SG = 4`.

Each theorem is proved by citing a theorem of `Lemmas.lean` with exactly
the same statement; the proofs there need not be read.

The development uses only the Lean core library (no Mathlib), contains
neither `sorry` nor `native_decide`, and is independent of the general
formalization of the Main Theorem.  `#print axioms` (at the end) reports at
most `propext`, `Quot.sound` and `Classical.choice`.
-/

namespace SGprimeDirect

open Form

/-- **`IL ⊕ S(G') = LC`.** -/
theorem IL_SG_eq_LC (φ : Form) : Thm [SG] φ ↔ Thm [LCax] φ := IL_SG_eq_LC_proof φ

/-- **`S(G')` is minimal in `CL`.** -/
theorem SG_minimal : MinimalCL SG := SG_minimal_proof

/-- **`S(G')` has order `4`.** -/
theorem SG_ord : ord SG = 4 := SG_ord_proof

end SGprimeDirect

#print axioms SGprimeDirect.IL_SG_eq_LC
#print axioms SGprimeDirect.SG_minimal
#print axioms SGprimeDirect.SG_ord
