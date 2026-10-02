/-!
# Definitions

This file contains everything needed to read the statements in
`SGprime/Main.lean`: formulas, Boolean validity (`CL`), minimality in `CL`,
the logics `IL ⊕ Ax`, the formula `S(G')` displayed in Corollary `cor:LC`,
and the axiom of `LC`.  It imports nothing.
-/

namespace SGprimeDirect

/-! ## Formulas -/

inductive Form where
  | var : Nat → Form
  | imp : Form → Form → Form
deriving Repr

open Form

infixr:25 " ⟶ " => Form.imp

def V (n : Nat) : Form := .var n

def subst (σ : Nat → Form) : Form → Form
  | var p => σ p
  | imp a b => imp (subst σ a) (subst σ b)

def eval (v : Nat → Bool) : Form → Bool
  | var p => v p
  | imp a b => !eval v a || eval v b

/-- Classical (Boolean) validity: membership in `CL`. -/
def Valid (f : Form) : Prop := ∀ v, eval v f = true

def ord : Form → Nat
  | var _ => 1
  | imp a b => max (ord a + 1) (ord b)

/-- `α` is minimal in `CL`: it is valid, and no valid formula is strictly
more general than `α` in the substitution preorder. -/
def MinimalCL (α : Form) : Prop :=
  Valid α ∧ ¬ ∃ β, Valid β ∧ (∃ σ, subst σ β = α) ∧ ¬ ∃ τ, subst τ α = β

/-! ## The logics `IL ⊕ Ax` -/

def axK (a b : Form) : Form := a ⟶ b ⟶ a
def axS (a b c : Form) : Form := (a ⟶ b ⟶ c) ⟶ (a ⟶ b) ⟶ a ⟶ c

/-- `Thm Ax` is the logic `IL ⊕ Ax`: the least set of formulas that
contains the axiom schemes `K` and `S` and every substitution instance of a
formula in `Ax`, and is closed under modus ponens.  Thus `Thm []` is `IL`.
(It is closed under substitution; see `ThmD.subst` in `Lemmas.lean`.) -/
inductive Thm (Ax : List Form) : Form → Prop
  | k (a b : Form) : Thm Ax (axK a b)
  | s (a b c : Form) : Thm Ax (axS a b c)
  | ax {B : Form} (h : B ∈ Ax) (σ : Nat → Form) : Thm Ax (subst σ B)
  | mp {a b : Form} : Thm Ax (a ⟶ b) → Thm Ax a → Thm Ax b

/-! ## The formulas `S(G')` and `LCax`

Variables `0,…,7` stand for `a, a', b', b, c'', c', c''', c`, and variable
`7 + i` is the extension variable `x_i`.  That `SG` is the translation of
`G'` (Definition `def:S`) is checked in `Lemmas.lean` (`SG_eq_translation`); this
is not needed for the claims. -/

/-- The formula `S(G')` displayed in Corollary `cor:LC`. -/
def SG : Form :=
  (V 9 ⟶ V 0 ⟶ V 1) ⟶ (V 11 ⟶ V 2 ⟶ V 3) ⟶
  (V 13 ⟶ V 4 ⟶ V 5) ⟶ (V 15 ⟶ V 6 ⟶ V 5) ⟶
  ((V 0 ⟶ V 3) ⟶ V 18) ⟶ (V 17 ⟶ V 18 ⟶ V 4) ⟶
  ((V 2 ⟶ V 1) ⟶ V 21) ⟶ (V 20 ⟶ V 21 ⟶ V 6) ⟶
  (V 25 ⟶ V 1 ⟶ V 2) ⟶ ((V 25 ⟶ V 4) ⟶ V 24) ⟶
  (V 28 ⟶ V 3 ⟶ V 0) ⟶ ((V 28 ⟶ V 6) ⟶ V 27) ⟶
  (V 29 ⟶ V 5 ⟶ V 7) ⟶ (V 26 ⟶ V 27 ⟶ V 29) ⟶
  (V 23 ⟶ V 24 ⟶ V 26) ⟶ ((V 23 ⟶ V 7) ⟶ V 22) ⟶
  ((V 20 ⟶ V 22) ⟶ V 19) ⟶ ((V 17 ⟶ V 19) ⟶ V 16) ⟶
  ((V 15 ⟶ V 16) ⟶ V 14) ⟶ ((V 13 ⟶ V 14) ⟶ V 12) ⟶
  ((V 11 ⟶ V 12) ⟶ V 10) ⟶ ((V 9 ⟶ V 10) ⟶ V 8) ⟶ V 8

/-- The axiom `((a → b) → c) → ((b → a) → c) → c` of `LC`. -/
def LCax : Form := ((V 0 ⟶ V 1) ⟶ V 2) ⟶ ((V 1 ⟶ V 0) ⟶ V 2) ⟶ V 2

end SGprimeDirect
