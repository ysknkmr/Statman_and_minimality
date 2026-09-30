/-!
# The polarized Statman translation preserves CL-minimality

Main results:
* `statman_minimalIn`: for every logic `Th` (`Logic Th`: closed under
  substitution and modus ponens, proves `γ → γ`, consistent), if `A` is
  minimal in `Th` and `statman A N ∈ Th`, then `statman A N` is minimal in
  `Th`;
* `statman_minimal`: the classical case (`Th = Valid`);
* `statman_ord`: `statman A N` has order at most four;
* `statman_valid`: `statman A N` is classically valid whenever `A` is.

Lean 4 core only (no Mathlib), no `sorry`.

Proof outline (see the paper):
1. `reduction`: to show `α` minimal it suffices that every proper
   *partial abstraction* `α'` (some occurrences of a subformula `D`
   replaced by a fresh `z`) is not valid.
2. `strict`: a proper partial abstraction of `A` is a strict
   generalization of `A`.
3. `decode`: every non-tail partial abstraction of `statman A N` is sent,
   by a suitable substitution, to `tautologies → B` where `B` is a proper
   partial abstraction of `A`.
-/

namespace StatmanMin

inductive Form where
  | var : Nat → Form
  | imp : Form → Form → Form
deriving DecidableEq, Repr

open Form

namespace Form

def subst (θ : Nat → Form) : Form → Form
  | var p   => θ p
  | imp a b => imp (subst θ a) (subst θ b)

/-- `Occ q f`: the variable `q` occurs in `f`. -/
def Occ (q : Nat) : Form → Prop
  | var p   => q = p
  | imp a b => Occ q a ∨ Occ q b

def eval (v : Nat → Bool) : Form → Bool
  | var p   => v p
  | imp a b => !eval v a || eval v b

def arrows : Form → Nat
  | var _   => 0
  | imp a b => arrows a + arrows b + 1

def leaves : Form → Nat
  | var _   => 1
  | imp a b => leaves a + leaves b

def maxVar : Form → Nat
  | var p   => p
  | imp a b => max (maxVar a) (maxVar b)

def chain : List Form → Form → Form
  | [],      r => r
  | L :: Ls, r => imp L (chain Ls r)

end Form

/-- Classical validity (Boolean semantics). -/
def Valid (f : Form) : Prop := ∀ v, f.eval v = true

/-- `Le β α`: `α` is a substitution instance of `β` (`β ≤sub α`). -/
def Le (β α : Form) : Prop := ∃ σ, β.subst σ = α

/-- Closed under substitution and modus ponens, and proving every `γ → γ`. -/
structure PreLogic (Th : Form → Prop) : Prop where
  subst : ∀ {t : Form}, Th t → ∀ θ : Nat → Form, Th (t.subst θ)
  mp    : ∀ {a b : Form}, Th (.imp a b) → Th a → Th b
  refl  : ∀ g : Form, Th (.imp g g)

/-- A logic: a consistent `PreLogic`. -/
structure Logic (Th : Form → Prop) : Prop extends PreLogic Th where
  cons  : ∀ p : Nat, ¬ Th (.var p)

/-- Minimality in a logic `Th` with respect to the substitution preorder. -/
def MinimalIn (Th : Form → Prop) (α : Form) : Prop :=
  Th α ∧ ∀ β, Th β → Le β α → Le α β

/-- Minimality in CL. -/
def Minimal (α : Form) : Prop := MinimalIn Valid α

/-! ## Basic lemmas -/

section Basic
open Form

theorem subst_congr {θ θ' : Nat → Form} :
    ∀ t : Form, (∀ q, Occ q t → θ q = θ' q) → t.subst θ = t.subst θ'
  | var p, h   => h p rfl
  | imp a b, h => by
      simp only [subst]
      rw [subst_congr a (fun q hq => h q (.inl hq)),
          subst_congr b (fun q hq => h q (.inr hq))]

theorem subst_var : ∀ t : Form, t.subst var = t
  | var _   => rfl
  | imp a b => by simp [subst, subst_var a, subst_var b]

theorem subst_subst (θ τ : Nat → Form) :
    ∀ t : Form, (t.subst θ).subst τ = t.subst (fun q => (θ q).subst τ)
  | var _   => rfl
  | imp a b => by simp [subst, subst_subst θ τ a, subst_subst θ τ b]

theorem eval_subst (v : Nat → Bool) (θ : Nat → Form) :
    ∀ t : Form, (t.subst θ).eval v = t.eval (fun q => (θ q).eval v)
  | var _   => rfl
  | imp a b => by simp [subst, eval, eval_subst v θ a, eval_subst v θ b]

theorem valid_subst {t : Form} (h : Valid t) (θ : Nat → Form) :
    Valid (t.subst θ) := fun v => by rw [eval_subst]; exact h _

theorem occ_subst {q x : Nat} {θ : Nat → Form} :
    ∀ {t : Form}, Occ q t → Occ x (θ q) → Occ x (t.subst θ)
  | var p, h, hx   => by simp only [Occ] at h; subst h; exact hx
  | imp a b, h, hx => h.elim (fun h => .inl (occ_subst h hx))
                             (fun h => .inr (occ_subst h hx))

theorem occ_le_maxVar {q : Nat} : ∀ {t : Form}, Occ q t → q ≤ t.maxVar
  | var p, h   => by simp only [Occ] at h; simp [maxVar, h]
  | imp a b, h => by
      simp only [maxVar]
      rcases h with h | h
      · exact Nat.le_trans (occ_le_maxVar h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (occ_le_maxVar h) (Nat.le_max_right _ _)

theorem arrows_subst_ge (θ : Nat → Form) :
    ∀ t : Form, t.arrows ≤ (t.subst θ).arrows
  | var _   => Nat.zero_le _
  | imp a b => by
      simp only [subst, arrows]
      have := arrows_subst_ge θ a; have := arrows_subst_ge θ b; omega

theorem subst_self_var {τ : Nat → Form} :
    ∀ {t : Form}, t.subst τ = t → ∀ {q}, Occ q t → τ q = var q
  | var p, h, q, hq   => by simp only [Occ] at hq; subst hq; exact h
  | imp a b, h, q, hq => by
      simp only [subst, imp.injEq] at h
      exact hq.elim (subst_self_var h.1) (subst_self_var h.2)

theorem eval_chain (v : Nat → Bool) (r : Form) :
    ∀ Ls : List Form,
      (chain Ls r).eval v = true ↔ ((∀ L ∈ Ls, L.eval v = true) → r.eval v = true)
  | []      => by simp [chain]
  | L :: Ls => by
      simp only [chain, eval, Bool.or_eq_true, Bool.not_eq_true', eval_chain v r Ls,
        List.mem_cons, forall_eq_or_imp]
      cases L.eval v <;> simp

theorem valid_of_chain {Ls : List Form} {r : Form} (h : Valid (chain Ls r))
    (hL : ∀ L ∈ Ls, Valid L) : Valid r :=
  fun v => (eval_chain v r Ls).1 (h v) (fun L hL' => hL L hL' v)

theorem PreLogic.of_chain {Th : Form → Prop} (hTh : PreLogic Th) {r : Form} :
    ∀ {Ls : List Form}, Th (chain Ls r) → (∀ L ∈ Ls, Th L) → Th r
  | [], h, _ => h
  | L :: _, h, hL => hTh.of_chain (hTh.mp h (hL L List.mem_cons_self))
      fun L' h' => hL L' (List.mem_cons_of_mem _ h')

theorem subst_chain (θ : Nat → Form) (r : Form) :
    ∀ Ls : List Form, (chain Ls r).subst θ = chain (Ls.map (·.subst θ)) (r.subst θ)
  | []      => rfl
  | L :: Ls => by simp [chain, subst, subst_chain θ r Ls]

theorem occ_chain {q : Nat} {r : Form} :
    ∀ {Ls : List Form}, Occ q (chain Ls r) ↔ (∃ L ∈ Ls, Occ q L) ∨ Occ q r
  | []      => by simp [chain]
  | L :: Ls => by simp [chain, Occ, occ_chain, or_assoc]

end Basic

/-! ## Partial abstraction -/

/-- `Repl D z t t'`: `t'` is `t` with some occurrences of `D` replaced by `z`. -/
inductive Repl (D : Form) (z : Nat) : Form → Form → Prop
  | refl (t) : Repl D z t t
  | hit : Repl D z D (.var z)
  | imp {a a' b b'} : Repl D z a a' → Repl D z b b' → Repl D z (.imp a b) (.imp a' b')

section ReplLemmas
open Form
variable {D : Form} {z : Nat}

theorem Repl.var_inv {q : Nat} {t' : Form} (h : Repl D z (var q) t') :
    t' = var q ∨ (D = var q ∧ t' = var z) := by
  cases h with
  | refl => exact .inl rfl
  | hit => exact .inr ⟨rfl, rfl⟩

theorem Repl.imp_inv {a b t' : Form} (h : Repl D z (Form.imp a b) t') :
    (D = Form.imp a b ∧ t' = var z) ∨
      ∃ a' b', t' = Form.imp a' b' ∧ Repl D z a a' ∧ Repl D z b b' := by
  cases h with
  | refl => exact .inr ⟨a, b, rfl, .refl _, .refl _⟩
  | hit => exact .inl ⟨rfl, rfl⟩
  | imp ha hb => exact .inr ⟨_, _, rfl, ha, hb⟩

theorem Repl.occ {t t' : Form} (h : Repl D z t t') {q : Nat} (hq : Occ q t') :
    Occ q t ∨ q = z := by
  induction h with
  | refl => exact .inl hq
  | hit => exact .inr hq
  | imp _ _ iha ihb =>
      rcases hq with hq | hq
      · exact (iha hq).imp_left .inl
      · exact (ihb hq).imp_left .inr

/-- If `z` appears in `t'` but not in `t`, then `D` occurs in `t`. -/
theorem Repl.occ_D {t t' : Form} (h : Repl D z t t') (hz' : Occ z t') (hz : ¬ Occ z t)
    {q : Nat} (hq : Occ q D) : Occ q t := by
  induction h with
  | refl => exact absurd hz' hz
  | hit => exact hq
  | imp _ _ iha ihb =>
      simp only [Occ, not_or] at hz hz'
      rcases hz' with h | h
      · exact .inl (iha h hz.1)
      · exact .inr (ihb h hz.2)

theorem leaves_pos : ∀ t : Form, 0 < t.leaves
  | var _ => Nat.one_pos
  | imp a _ => by have := leaves_pos a; simp only [leaves]; omega

theorem Repl.eq_of_leaves {t t' : Form} (h : Repl D z t t') (hl : t.leaves < D.leaves) :
    t' = t := by
  induction h with
  | refl => rfl
  | hit => omega
  | imp _ _ iha ihb =>
      simp only [leaves] at hl
      have := leaves_pos ‹Form›
      rw [iha (by omega), ihb (by omega)]

/-- Undoing a partial abstraction. -/
theorem Repl.subst_back {t t' : Form} (h : Repl D z t t') (hz : ¬ Occ z t) :
    t'.subst (fun q => if q = z then D else var q) = t := by
  induction h with
  | refl t =>
      rw [subst_congr t (θ' := var) (fun q hq => by
        have : q ≠ z := fun e => hz (e ▸ hq)
        simp [this]), subst_var]
  | hit => simp [subst]
  | imp _ _ iha ihb =>
      simp only [Occ, not_or] at hz
      simp [subst, iha hz.1, ihb hz.2]

theorem Repl.arrows_le {t t' : Form} (h : Repl D z t t') : t'.arrows ≤ t.arrows := by
  induction h with
  | refl => exact Nat.le_refl _
  | hit => exact Nat.zero_le _
  | imp _ _ iha ihb => simp only [arrows]; omega

theorem Repl.arrows_lt {t t' : Form} (h : Repl D z t t') (hD : ∀ p, D ≠ var p)
    (hz' : Occ z t') (hz : ¬ Occ z t) : t'.arrows < t.arrows := by
  induction h with
  | refl => exact absurd hz' hz
  | hit =>
      cases hD' : D with
      | var p => exact absurd hD' (hD p)
      | imp => simp [arrows]
  | imp ha hb iha ihb =>
      simp only [Occ, not_or] at hz hz'
      simp only [arrows]
      have := ha.arrows_le; have := hb.arrows_le
      rcases hz' with h | h
      · have := iha h hz.1; omega
      · have := ihb h hz.2; omega

theorem Repl.var_subst {p : Nat} {τ : Nat → Form} {t t' : Form}
    (h : Repl (var p) z t t') (ht : t.subst τ = t') (hz : ¬ Occ z t) (hp : p ≠ z) :
    (Occ p t' → τ p = var p) ∧ (Occ z t' → τ p = var z) := by
  induction h with
  | refl t =>
      exact ⟨fun hq => subst_self_var ht hq, fun hq => absurd hq hz⟩
  | hit =>
      simp only [subst] at ht
      exact ⟨fun hq => absurd hq hp, fun _ => ht⟩
  | imp _ _ iha ihb =>
      simp only [subst, Form.imp.injEq] at ht
      simp only [Occ, not_or] at hz
      have ha := iha ht.1 hz.1; have hb := ihb ht.2 hz.2
      exact ⟨fun hq => hq.elim ha.1 hb.1, fun hq => hq.elim ha.2 hb.2⟩

end ReplLemmas

/-! ## Reduction lemma and strictness -/

section Reduction
open Form

/-- Replacing the variable `q` by `z` in a generalization `β` of `α`
gives a partial abstraction of `α`. -/
theorem repl_update (σ : Nat → Form) (q z : Nat) :
    ∀ β : Form, Repl (σ q) z (β.subst σ)
      (β.subst (fun r => if r = q then var z else σ r))
  | var r   => by
      by_cases h : r = q
      · subst h; simp [subst]; exact .hit
      · simp [subst, h]; exact .refl _
  | imp a b => .imp (repl_update σ q z a) (repl_update σ q z b)

/-- To prove `α` minimal it suffices to refute every proper partial
abstraction by a fresh variable `z ≥ bound`. -/
theorem reduction {Th : Form → Prop} (hTh : Logic Th) {α : Form} (bound : Nat)
    (hα : Th α)
    (h : ∀ D z α', bound ≤ z → ¬ Occ z α → Repl D z α α' → Occ z α' →
      (∀ p, D = var p → Occ p α') → ¬ Th α') :
    MinimalIn Th α := by
  classical
  refine ⟨hα, fun β hβ ⟨σ, hσ⟩ => ?_⟩
  let z := max bound (α.maxVar + 1)
  have hzb : bound ≤ z := Nat.le_max_left _ _
  have hzα : ¬ Occ z α := fun hz =>
    have := occ_le_maxVar hz; by omega
  -- a bad variable `q` gives a valid proper partial abstraction
  have bad : ∀ q, Occ q β → ((∀ p, σ q ≠ var p) ∨
      ∃ q', Occ q' β ∧ q' ≠ q ∧ σ q' = σ q) → False := by
    intro q hq hbad
    let σ' := fun r => if r = q then var z else σ r
    have hR := repl_update σ q z β
    rw [hσ] at hR
    refine h (σ q) z _ hzb hzα hR (occ_subst hq (by simp [Occ])) ?_
      (hTh.subst hβ σ')
    intro p hp
    rcases hbad with hb | ⟨q', hq', hne, he⟩
    · exact absurd hp (hb p)
    · exact occ_subst hq' (by simp [hne, he, hp, Occ])
  -- otherwise `σ` is an injective renaming on the variables of `β`
  have hvar : ∀ q, Occ q β → ∃ p, σ q = var p := fun q hq =>
    Classical.byContradiction fun hn =>
      bad q hq (.inl fun p hp => hn ⟨p, hp⟩)
  let τ : Nat → Form := fun r =>
    if hr : ∃ q, Occ q β ∧ σ q = var r then var (Classical.choose hr) else var r
  refine ⟨τ, ?_⟩
  rw [← hσ, subst_subst]
  conv => rhs; rw [← subst_var β]
  apply subst_congr
  intro q hq
  obtain ⟨p, hp⟩ := hvar q hq
  have hex : ∃ q, Occ q β ∧ σ q = var p := ⟨q, hq, hp⟩
  simp only [hp, subst, τ, hex, dite_true]
  have hs := Classical.choose_spec hex
  refine Classical.byContradiction fun hne => ?_
  exact bad q hq (.inr ⟨_, hs.1, fun e => hne (by rw [e]), by rw [hs.2, hp]⟩)

/-- A proper partial abstraction of a minimal formula is not valid. -/
theorem strict {Th : Form → Prop} {A B D₀ : Form} {y : Nat} (hA : MinimalIn Th A) (hR : Repl D₀ y A B)
    (hyA : ¬ Occ y A) (hyB : Occ y B)
    (hvar : ∀ p, D₀ = var p → p ≠ y ∧ Occ p B) : ¬ Th B := by
  intro hB
  obtain ⟨τ, hτ⟩ := hA.2 B hB ⟨_, hR.subst_back hyA⟩
  by_cases hD : ∃ p, D₀ = var p
  · obtain ⟨p, rfl⟩ := hD
    obtain ⟨hpy, hpB⟩ := hvar p rfl
    have := hR.var_subst hτ hyA hpy
    have := this.1 hpB ▸ this.2 hyB
    exact hpy (by injection this)
  · have := hR.arrows_lt (fun p e => hD ⟨p, e⟩) hyB hyA
    have := arrows_subst_ge τ A
    rw [hτ] at this; omega

end Reduction

/-! ## The polarized Statman translation -/

section Translation
open Form

/-- A link with the given body and head: `body → head` at positive
polarity, `head → body` at negative polarity. -/
def mk (pos : Bool) (body head : Form) : Form :=
  if pos then imp body head else imp head body

/-- `tr A pos n = (representative, links)`. Implication occurrences get the
fresh variables `n, n+1, …, n + arrows A - 1` in pre-order. -/
def tr : Form → Bool → Nat → Form × List Form
  | var p,   _,   _ => (var p, [])
  | imp A B, pos, n =>
      let a := tr A (!pos) (n + 1)
      let b := tr B pos (n + 1 + A.arrows)
      (var n, a.2 ++ b.2 ++ [mk pos (imp a.1 b.1) (var n)])

/-- The polarized Statman translation, with fresh variables from `n` on. -/
def statman (A : Form) (n : Nat) : Form := chain (tr A true n).2 (tr A true n).1

theorem subst_mk (θ : Nat → Form) (pos : Bool) (c h : Form) :
    (mk pos c h).subst θ = mk pos (c.subst θ) (h.subst θ) := by
  cases pos <;> rfl

theorem PreLogic.mk_refl {Th : Form → Prop} (hTh : PreLogic Th) (pos : Bool) (c : Form) :
    Th (StatmanMin.mk pos c c) := by
  cases pos <;> exact hTh.refl c

theorem occ_mk {q : Nat} {pos : Bool} {c h : Form} :
    Occ q (mk pos c h) ↔ Occ q c ∨ Occ q h := by
  cases pos <;> simp [mk, Occ, or_comm]

/-- Soundness of the translation (the only place where polarity matters). -/
theorem tr_sound (v : Nat → Bool) :
    ∀ (A : Form) (pos : Bool) (n : Nat), (∀ L ∈ (tr A pos n).2, L.eval v = true) →
      (pos = true → A.eval v = true → (tr A pos n).1.eval v = true) ∧
      (pos = false → (tr A pos n).1.eval v = true → A.eval v = true)
  | var p, pos, n, _ => by simp [tr]
  | imp A B, pos, n, h => by
      simp only [tr, List.mem_append, List.mem_singleton] at h ⊢
      have hA := tr_sound v A (!pos) (n + 1) (fun L hL => h L (.inl (.inl hL)))
      have hB := tr_sound v B pos (n + 1 + A.arrows) (fun L hL => h L (.inl (.inr hL)))
      have hl := h _ (.inr rfl)
      cases pos <;> simp [mk, eval] at hA hB hl ⊢ <;> grind

theorem statman_valid {A : Form} (hA : Valid A) (n : Nat) : Valid (statman A n) := by
  intro v
  simp only [statman, eval_chain]
  exact fun h => (tr_sound v A true n h).1 rfl (hA v)

/-- The representative is a variable: the atom itself, or the fresh `n`. -/
theorem tr_fst (A : Form) (pos : Bool) (n : Nat) :
    (∃ p, A = var p ∧ (tr A pos n).1 = var p) ∨ ((tr A pos n).1 = var n ∧ 0 < A.arrows) := by
  cases A with
  | var p => exact .inl ⟨p, rfl, rfl⟩
  | imp => right; simp [tr, arrows]

theorem occ_tr_fst {A : Form} {pos : Bool} {n q : Nat} (h : Occ q (tr A pos n).1) :
    Occ q A ∨ (n ≤ q ∧ q < n + A.arrows) := by
  rcases tr_fst A pos n with ⟨p, rfl, e⟩ | ⟨e, hpos⟩
  · rw [e] at h; exact .inl h
  · rw [e] at h; simp only [Occ] at h; right; omega

theorem occ_tr_snd :
    ∀ {A : Form} {pos : Bool} {n q : Nat}, ∀ L ∈ (tr A pos n).2, Occ q L →
      Occ q A ∨ (n ≤ q ∧ q < n + A.arrows)
  | var p, pos, n, q, L, hL, _ => by simp [tr] at hL
  | imp A B, pos, n, q, L, hL, hq => by
      simp only [tr, List.mem_append, List.mem_singleton] at hL
      simp only [Occ, arrows]
      rcases hL with (hL | hL) | rfl
      · rcases occ_tr_snd L hL hq with h | h
        · exact .inl (.inl h)
        · right; omega
      · rcases occ_tr_snd L hL hq with h | h
        · exact .inl (.inr h)
        · right; omega
      · rcases occ_mk.1 hq with h | h
        · rcases h with h | h
          · rcases occ_tr_fst h with h | h
            · exact .inl (.inl h)
            · right; omega
          · rcases occ_tr_fst h with h | h
            · exact .inl (.inr h)
            · right; omega
        · simp only [Occ] at h; right; omega

theorem leaves_tr_snd :
    ∀ {A : Form} {pos : Bool} {n : Nat}, ∀ L ∈ (tr A pos n).2, L.leaves = 3
  | var p, pos, n, L, hL => by simp [tr] at hL
  | imp A B, pos, n, L, hL => by
      simp only [tr, List.mem_append, List.mem_singleton] at hL
      rcases hL with (hL | hL) | rfl
      · exact leaves_tr_snd L hL
      · exact leaves_tr_snd L hL
      · rcases tr_fst A (!pos) (n + 1) with ⟨_, _, ea⟩ | ⟨ea, _⟩ <;>
        rcases tr_fst B pos (n + 1 + A.arrows) with ⟨_, _, eb⟩ | ⟨eb, _⟩ <;>
        · rw [ea, eb]; cases pos <;> rfl

end Translation

/-! ## Pointwise relations on lists and partial abstractions of chains -/

inductive Pw (R : Form → Form → Prop) : List Form → List Form → Prop
  | nil : Pw R [] []
  | cons {a a' l l'} : R a a' → Pw R l l' → Pw R (a :: l) (a' :: l')

section PwLemmas
variable {R : Form → Form → Prop}

theorem Pw.append_inv :
    ∀ {l₁ l₂ l' : List Form}, Pw R (l₁ ++ l₂) l' →
      ∃ l₁' l₂', l' = l₁' ++ l₂' ∧ Pw R l₁ l₁' ∧ Pw R l₂ l₂'
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons ha h =>
      let ⟨l₁', l₂', e, h₁, h₂⟩ := Pw.append_inv h
      ⟨_ :: l₁', l₂', by rw [e]; rfl, .cons ha h₁, h₂⟩

theorem Pw.single_inv {a : Form} {l' : List Form} (h : Pw R [a] l') :
    ∃ a', l' = [a'] ∧ R a a' := by
  cases h with
  | cons ha h => cases h; exact ⟨_, rfl, ha⟩

theorem Pw.mem_inv : ∀ {l l' : List Form}, Pw R l l' → ∀ {a'}, a' ∈ l' → ∃ a ∈ l, R a a'
  | _, _, .cons ha h, _, hm => by
      rcases List.mem_cons.1 hm with rfl | hm
      · exact ⟨_, List.mem_cons_self, ha⟩
      · obtain ⟨a, ha', hr⟩ := h.mem_inv hm
        exact ⟨a, List.mem_cons_of_mem _ ha', hr⟩

end PwLemmas

section ChainRepl
open Form
variable {D : Form} {z : Nat}

/-- A partial abstraction of a chain either works pointwise, or replaces a
nonempty tail of the chain. -/
theorem chain_repl {r : Form} :
    ∀ {Ls : List Form} {α' : Form}, Repl D z (chain Ls r) α' →
      (∃ Ls' r', α' = chain Ls' r' ∧ Pw (Repl D z) Ls Ls' ∧ Repl D z r r') ∨
      (∃ L Ls₁ Ls₂ Ls₁', Ls = Ls₁ ++ L :: Ls₂ ∧ D = chain (L :: Ls₂) r ∧
        α' = chain Ls₁' (var z) ∧ Pw (Repl D z) Ls₁ Ls₁')
  | [], _, h => .inl ⟨[], _, rfl, .nil, h⟩
  | L :: Ls, α', h => by
      rcases Repl.imp_inv h with ⟨hD, rfl⟩ | ⟨a', b', rfl, ha, hb⟩
      · exact .inr ⟨L, [], Ls, [], rfl, hD, rfl, .nil⟩
      · rcases chain_repl hb with ⟨Ls', r', rfl, h1, h2⟩ | ⟨L', Ls₁, Ls₂, Ls₁', e, hD, rfl, h1⟩
        · exact .inl ⟨a' :: Ls', r', rfl, .cons ha h1, h2⟩
        · exact .inr ⟨L', L :: Ls₁, Ls₂, a' :: Ls₁', by rw [e]; rfl, hD, rfl, .cons ha h1⟩

/-- Partial abstraction of a link. -/
theorem mk_repl {pos : Bool} {a b : Form} {x : Nat} {E' : Form}
    (h : Repl D z (mk pos (imp a b) (var x)) E') :
    (D = mk pos (imp a b) (var x) ∧ E' = var z) ∨
    (D = imp a b ∧ E' = mk pos (var z) (var x)) ∨
    (∃ a' b' h', E' = mk pos (imp a' b') h' ∧ Repl D z a a' ∧ Repl D z b b' ∧
      (h' = var x ∨ (D = var x ∧ h' = var z))) := by
  have key : ∀ c', Repl D z (imp a b) c' → ∀ h', Repl D z (var x) h' →
      (D = imp a b ∧ mk pos c' h' = mk pos (var z) (var x)) ∨
      ∃ a' b' h'', mk pos c' h' = mk pos (imp a' b') h'' ∧ Repl D z a a' ∧ Repl D z b b' ∧
        (h'' = var x ∨ (D = var x ∧ h'' = var z)) := by
    intro c' hc h' hh
    rcases Repl.imp_inv hc with ⟨hD, rfl⟩ | ⟨a', b', rfl, ha, hb⟩
    · rcases Repl.var_inv hh with rfl | ⟨hD', _⟩
      · exact .inl ⟨hD, rfl⟩
      · rw [hD] at hD'; cases hD'
    · exact .inr ⟨a', b', h', rfl, ha, hb, Repl.var_inv hh⟩
  cases pos
  · rcases Repl.imp_inv h with ⟨hD, rfl⟩ | ⟨h', c', rfl, hh, hc⟩
    · exact .inl ⟨hD, rfl⟩
    · exact .inr (key c' hc h' hh)
  · rcases Repl.imp_inv h with ⟨hD, rfl⟩ | ⟨c', h', rfl, hc, hh⟩
    · exact .inl ⟨hD, rfl⟩
    · exact .inr (key c' hc h' hh)

end ChainRepl

/-! ## Decoding partial abstractions of the translation -/

section Decode
open Form Classical

/-- `D` has the shape of a link. -/
def IsLink (D : Form) : Prop := ∃ pos a b x, D = mk pos (imp a b) (var x)

/-- `q` occurs in one of the formulas `Ls` or in `r`. -/
def OccL (q : Nat) (Ls : List Form) (r : Form) : Prop := (∃ L ∈ Ls, Occ q L) ∨ Occ q r

theorem not_isLink_var (p : Nat) : ¬ IsLink (var p) := by
  rintro ⟨pos, a, b, x, h⟩; cases pos <;> simp [mk] at h

theorem not_isLink_body (p q : Nat) : ¬ IsLink (imp (var p) (var q)) := by
  rintro ⟨pos, a, b, x, h⟩; cases pos <;> simp [mk] at h

theorem occL_append {q : Nat} {L1 L2 : List Form} {E r : Form} :
    OccL q (L1 ++ L2 ++ [E]) r ↔ (∃ L ∈ L1, Occ q L) ∨ (∃ L ∈ L2, Occ q L) ∨ Occ q E ∨ Occ q r := by
  simp only [OccL, List.mem_append, List.mem_singleton]
  constructor
  · rintro (⟨L, (hL | hL) | rfl, h⟩ | h)
    · exact .inl ⟨L, hL, h⟩
    · exact .inr (.inl ⟨L, hL, h⟩)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · rintro (⟨L, hL, h⟩ | ⟨L, hL, h⟩ | h | h)
    · exact .inl ⟨L, .inl (.inl hL), h⟩
    · exact .inl ⟨L, .inl (.inr hL), h⟩
    · exact .inl ⟨E, .inr rfl, h⟩
    · exact .inr h

variable {D : Form} {z : Nat}

theorem occL_region {P : Nat → Prop} {Ls Ls' : List Form} {a a' : Form}
    (reg : ∀ L ∈ Ls, ∀ q, Occ q L → P q) (regr : ∀ q, Occ q a → P q)
    (hL : Pw (Repl D z) Ls Ls') (hr : Repl D z a a') {q : Nat} (hq : OccL q Ls' a') :
    q = z ∨ P q := by
  rcases hq with ⟨L', hL', hq⟩ | hq
  · obtain ⟨L, hL0, hR⟩ := hL.mem_inv hL'
    exact (hR.occ hq).elim (fun h => .inr (reg L hL0 q h)) .inl
  · exact (hr.occ hq).elim (fun h => .inr (regr q h)) .inl

/-- If `D` mentions a variable outside the region, nothing was replaced. -/
theorem occL_zfree {P : Nat → Prop} {Ls Ls' : List Form} {a a' : Form}
    (reg : ∀ L ∈ Ls, ∀ q, Occ q L → P q) (regr : ∀ q, Occ q a → P q)
    (hL : Pw (Repl D z) Ls Ls') (hr : Repl D z a a') (hz : ¬ P z)
    {x : Nat} (hxD : Occ x D) (hx : ¬ P x) : ¬ OccL z Ls' a' := by
  rintro (⟨L', hL', hq⟩ | hq)
  · obtain ⟨L, hL0, hR⟩ := hL.mem_inv hL'
    exact hx (reg L hL0 x (hR.occ_D hq (fun h => hz (reg L hL0 z h)) hxD))
  · exact hx (regr x (hr.occ_D hq (fun h => hz (regr z h)) hxD))

variable (D z) (N : Nat) (ζ : Form) (Th : Form → Prop)

/-- What the decoding of a subtree provides. `B` is the decoded formula,
`θ` the decoding substitution; `z` also plays the role of the fresh
variable in `B`. -/
structure Good (n : Nat) (A : Form) (Ls' : List Form) (r' B : Form) (θ : Nat → Form) :
    Prop where
  out   : ∀ q, (q < n ∨ n + A.arrows ≤ q) → q ≠ z → θ q = var q
  links : ∀ L ∈ Ls', Th (L.subst θ)
  rep   : r'.subst θ = B
  zval  : OccL z Ls' r' → θ z = ζ ∨ ∃ x, D = var x ∧ n ≤ x ∧ x < n + A.arrows
  nz    : ¬ OccL z Ls' r' → B = A
  zocc  : OccL z Ls' r' → Occ z B
  pocc  : ∀ p, D = var p → p < N → OccL p Ls' r' → Occ p B
  d0    : OccL z Ls' r' → ∃ D₀, Repl D₀ z A B ∧ (∀ p, D₀ = var p → D₀ = D ∧ p < N) ∧
            (D₀ ≠ D → ∃ x, Occ x D ∧ n ≤ x ∧ x < n + A.arrows)

end Decode

section DecodeProof
open Form Classical
variable {D : Form} {z N : Nat} {ζ : Form} {Th : Form → Prop}

/-- The inductive step of the decoding, for an implication node `n`
with children data abstracted. -/
theorem decode_node (hTh : PreLogic Th) (hζL : IsLink D → Th ζ) (hζ : ¬ IsLink D → ζ = var z)
    {A1 A2 a1 b1 E' r' : Form} {pos : Bool} {n : Nat} {Ls1 Ls2 L1' L2' : List Form}
    (hA : ∀ q, Occ q (imp A1 A2) → q < N) (hN : N ≤ n)
    (hz : n + (A1.arrows + A2.arrows + 1) ≤ z)
    (reg1 : ∀ L ∈ Ls1, ∀ q, Occ q L → Occ q A1 ∨ (n + 1 ≤ q ∧ q < n + 1 + A1.arrows))
    (regr1 : ∀ q, Occ q a1 → Occ q A1 ∨ (n + 1 ≤ q ∧ q < n + 1 + A1.arrows))
    (sh1 : (∃ p, A1 = var p ∧ a1 = var p) ∨ (a1 = var (n + 1) ∧ 0 < A1.arrows))
    (reg2 : ∀ L ∈ Ls2, ∀ q, Occ q L → Occ q A2 ∨
      (n + 1 + A1.arrows ≤ q ∧ q < n + 1 + A1.arrows + A2.arrows))
    (regr2 : ∀ q, Occ q b1 → Occ q A2 ∨
      (n + 1 + A1.arrows ≤ q ∧ q < n + 1 + A1.arrows + A2.arrows))
    (sh2 : (∃ p, A2 = var p ∧ b1 = var p) ∨
      (b1 = var (n + 1 + A1.arrows) ∧ 0 < A2.arrows))
    (h1 : Pw (Repl D z) Ls1 L1') (h2 : Pw (Repl D z) Ls2 L2')
    (hE : Repl D z (mk pos (imp a1 b1) (var n)) E') (hr : Repl D z (var n) r')
    (hx : ∀ x, D = var x → n ≤ x → x < n + (A1.arrows + A2.arrows + 1) →
      OccL x (L1' ++ L2' ++ [E']) r')
    (IH1 : ∀ c1, Repl D z a1 c1 →
      (∀ x, D = var x → n + 1 ≤ x → x < n + 1 + A1.arrows → OccL x L1' c1) →
      ∃ B θ, Good D z N ζ Th (n + 1) A1 L1' c1 B θ)
    (IH2 : ∀ c2, Repl D z b1 c2 →
      (∀ x, D = var x → n + 1 + A1.arrows ≤ x → x < n + 1 + A1.arrows + A2.arrows →
        OccL x L2' c2) →
      ∃ B θ, Good D z N ζ Th (n + 1 + A1.arrows) A2 L2' c2 B θ) :
    ∃ B θ, Good D z N ζ Th n (imp A1 A2) (L1' ++ L2' ++ [E']) r' B θ := by
  have har : (imp A1 A2).arrows = A1.arrows + A2.arrows + 1 := rfl
  have hA1 : ∀ q, Occ q A1 → q < N := fun q h => hA q (.inl h)
  have hA2 : ∀ q, Occ q A2 → q < N := fun q h => hA q (.inr h)
  -- regions of the two children
  have loc1 : ∀ {c1}, Repl D z a1 c1 → ∀ {q}, OccL q L1' c1 →
      q = z ∨ q < N ∨ (n + 1 ≤ q ∧ q < n + 1 + A1.arrows) := fun {_} hc {_} hq =>
    (occL_region reg1 regr1 h1 hc hq).imp_right (Or.imp_left (hA1 _))
  have loc2 : ∀ {c2}, Repl D z b1 c2 → ∀ {q}, OccL q L2' c2 →
      q = z ∨ q < N ∨ (n + 1 + A1.arrows ≤ q ∧ q < n + 1 + A1.arrows + A2.arrows) :=
    fun {_} hc {_} hq => (occL_region reg2 regr2 h2 hc hq).imp_right (Or.imp_left (hA2 _))
  have free1 : ∀ {c1}, Repl D z a1 c1 → ∀ {x}, Occ x D → ¬ x < N →
      ¬ (n + 1 ≤ x ∧ x < n + 1 + A1.arrows) → ¬ OccL z L1' c1 :=
    fun {_} hc {x} hxD hx1 hx2 => occL_zfree reg1 regr1 h1 hc
      (fun h => h.elim (fun h => absurd (hA1 z h) (by omega)) (fun h => by omega))
      hxD (fun h => h.elim (fun h => hx1 (hA1 x h)) hx2)
  have free2 : ∀ {c2}, Repl D z b1 c2 → ∀ {x}, Occ x D → ¬ x < N →
      ¬ (n + 1 + A1.arrows ≤ x ∧ x < n + 1 + A1.arrows + A2.arrows) → ¬ OccL z L2' c2 :=
    fun {_} hc {x} hxD hx1 hx2 => occL_zfree reg2 regr2 h2 hc
      (fun h => h.elim (fun h => absurd (hA2 z h) (by omega)) (fun h => by omega))
      hxD (fun h => h.elim (fun h => hx1 (hA2 x h)) hx2)
  -- gluing the two decoding substitutions
  have combine : ∀ {c1 c2 B1 B2 : Form} {θ1 θ2 : Nat → Form},
      Repl D z a1 c1 → Repl D z b1 c2 →
      Good D z N ζ Th (n + 1) A1 L1' c1 B1 θ1 →
      Good D z N ζ Th (n + 1 + A1.arrows) A2 L2' c2 B2 θ2 → ∀ θn ζz : Form, ∃ θ : Nat → Form,
        (∀ q, (q < n ∨ n + (A1.arrows + A2.arrows + 1) ≤ q) → q ≠ z → θ q = var q) ∧
        (∀ L ∈ L1', Th (L.subst θ)) ∧ (∀ L ∈ L2', Th (L.subst θ)) ∧
        c1.subst θ = B1 ∧ c2.subst θ = B2 ∧ θ n = θn ∧
        θ z = (if OccL z L1' c1 then θ1 z else if OccL z L2' c2 then θ2 z else ζz) := by
    intro c1 c2 B1 B2 θ1 θ2 hc1 hc2 G1 G2 θn ζz
    have cons : OccL z L1' c1 → OccL z L2' c2 → θ1 z = θ2 z := by
      intro o1 o2
      rcases G1.zval o1 with e1 | ⟨x, hDx, hx1, hx2⟩
      · rcases G2.zval o2 with e2 | ⟨x, hDx, hx1, hx2⟩
        · rw [e1, e2]
        · exact absurd o1 (free1 hc1 (x := x) (by simp [hDx, Occ]) (by omega) (by omega))
      · exact absurd o2 (free2 hc2 (x := x) (by simp [hDx, Occ]) (by omega) (by omega))
    let θz := if OccL z L1' c1 then θ1 z else if OccL z L2' c2 then θ2 z else ζz
    let θ : Nat → Form := fun q => if q = z then θz else if q = n then θn else
      if q < n + 1 + A1.arrows then θ1 q else θ2 q
    have ag1 : ∀ t : Form, (∀ q, Occ q t → OccL q L1' c1) → t.subst θ = t.subst θ1 := by
      intro t ht
      apply subst_congr
      intro q hq
      rcases loc1 hc1 (ht q hq) with rfl | h | h
      · simp [θ, θz, ht q hq]
      · have : q ≠ z := by omega
        simp [θ, this, show q ≠ n by omega, show q < n + 1 + A1.arrows by omega]
      · have : q ≠ z := by omega
        simp [θ, this, show q ≠ n by omega, show q < n + 1 + A1.arrows by omega]
    have ag2 : ∀ t : Form, (∀ q, Occ q t → OccL q L2' c2) → t.subst θ = t.subst θ2 := by
      intro t ht
      apply subst_congr
      intro q hq
      rcases loc2 hc2 (ht q hq) with rfl | h | h
      · by_cases o1 : OccL q L1' c1
        · simp [θ, θz, o1, cons o1 (ht q hq)]
        · simp [θ, θz, o1, ht q hq]
      · have : q ≠ z := by omega
        simp only [θ, this, show q ≠ n by omega, show q < n + 1 + A1.arrows by omega,
          ite_false, ite_true]
        rw [G1.out q (.inl (by omega)) this, G2.out q (.inl (by omega)) this]
      · have : q ≠ z := by omega
        simp [θ, this, show q ≠ n by omega, show ¬ q < n + 1 + A1.arrows by omega]
    refine ⟨θ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq hqz
      rcases hq with hq | hq
      · simp only [θ, hqz, show q ≠ n by omega, show q < n + 1 + A1.arrows by omega,
          ite_false, ite_true]
        exact G1.out q (.inl (by omega)) hqz
      · simp only [θ, hqz, show q ≠ n by omega, show ¬ q < n + 1 + A1.arrows by omega,
          ite_false]
        exact G2.out q (.inr (by omega)) hqz
    · intro L hL
      rw [ag1 L (fun q hq => .inl ⟨L, hL, hq⟩)]; exact G1.links L hL
    · intro L hL
      rw [ag2 L (fun q hq => .inl ⟨L, hL, hq⟩)]; exact G2.links L hL
    · rw [ag1 c1 (fun q hq => .inr hq)]; exact G1.rep
    · rw [ag2 c2 (fun q hq => .inr hq)]; exact G2.rep
    · simp [θ, show n ≠ z by omega]
    · simp [θ, θz]
  -- the parent's view of the children
  have up1 : ∀ {q c1 c2 r}, OccL q L1' c1 → OccL q (L1' ++ L2' ++ [mk pos (imp c1 c2) (var n)]) r :=
    fun h => occL_append.2 (h.elim .inl (fun h => .inr (.inr (.inl (occ_mk.2 (.inl (.inl h)))))))
  have up2 : ∀ {q c1 c2 r}, OccL q L2' c2 → OccL q (L1' ++ L2' ++ [mk pos (imp c1 c2) (var n)]) r :=
    fun h => occL_append.2 (h.elim (fun h => .inr (.inl h))
      (fun h => .inr (.inr (.inl (occ_mk.2 (.inl (.inr h)))))))
  have down : ∀ {q c1 c2 h' r}, OccL q (L1' ++ L2' ++ [mk pos (imp c1 c2) h']) r →
      OccL q L1' c1 ∨ OccL q L2' c2 ∨ Occ q h' ∨ Occ q r := by
    intro q c1 c2 h' r h
    rcases occL_append.1 h with h | h | h | h
    · exact .inl (.inl h)
    · exact .inr (.inl (.inl h))
    · rcases occ_mk.1 h with (h | h) | h
      · exact .inl (.inr h)
      · exact .inr (.inl (.inr h))
      · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  have hmk : ∀ c h' x, mk pos c h' ≠ var x := by intro c h' x; cases pos <;> simp [mk]
  -- the node itself is replaced: `B = z`
  rcases mk_repl hE with ⟨hD, rfl⟩ | ⟨hD, rfl⟩ | ⟨a', b', h', rfl, ha', hb', hh'⟩
  · -- the whole link is replaced
    have hnD : Occ n D := by rw [hD]; exact occ_mk.2 (.inr rfl)
    have hr' : r' = var n := by
      rcases Repl.var_inv hr with h | ⟨hDn, _⟩
      · exact h
      · exact absurd (hD.symm.trans hDn) (hmk _ _ _)
    subst hr'
    obtain ⟨B1, θ1, G1⟩ := IH1 a1 (.refl _) (fun x h => absurd (hD.symm.trans h) (hmk _ _ _))
    obtain ⟨B2, θ2, G2⟩ := IH2 b1 (.refl _) (fun x h => absurd (hD.symm.trans h) (hmk _ _ _))
    obtain ⟨θ, hout, hl1, hl2, -, -, hn, hθz⟩ := combine (.refl _) (.refl _) G1 G2 (var z) ζ
    have o1 := free1 (.refl _) hnD (by omega) (by omega)
    have o2 := free2 (.refl _) hnD (by omega) (by omega)
    simp only [o1, o2, ite_false] at hθz
    refine ⟨var z, θ, ⟨hout, ?_, by simp [subst, hn], fun _ => .inl hθz,
      fun h => (h (occL_append.2 (.inr (.inr (.inl (show Occ z (var z) from rfl)))))).elim, fun _ => rfl,
      fun p hp => absurd (hD.symm.trans hp) (hmk _ _ _),
      fun _ => ⟨imp A1 A2, .hit, (fun p hp => by cases hp),
        fun _ => ⟨n, hnD, Nat.le_refl _, by omega⟩⟩⟩⟩
    intro L hL
    simp only [List.mem_append, List.mem_singleton] at hL
    rcases hL with (hL | hL) | rfl
    · exact hl1 L hL
    · exact hl2 L hL
    · simp only [subst, hθz]; exact hζL ⟨pos, a1, b1, n, hD⟩
  · -- the body is replaced
    have hbody : ∃ p q, D = imp (var p) (var q) := by
      rcases sh1 with ⟨p, _, rfl⟩ | ⟨rfl, _⟩ <;> rcases sh2 with ⟨q, _, rfl⟩ | ⟨rfl, _⟩ <;>
        exact ⟨_, _, hD⟩
    obtain ⟨p0, q0, hD0⟩ := hbody
    have hζz : ζ = var z := hζ (hD0 ▸ not_isLink_body p0 q0)
    have hDv : ∀ x, D ≠ var x := fun x h => by rw [hD0] at h; cases h
    have hr' : r' = var n := by
      rcases Repl.var_inv hr with h | ⟨hDn, _⟩
      · exact h
      · exact absurd hDn (hDv n)
    subst hr'
    obtain ⟨B1, θ1, G1⟩ := IH1 a1 (.refl _) (fun x h => absurd h (hDv x))
    obtain ⟨B2, θ2, G2⟩ := IH2 b1 (.refl _) (fun x h => absurd h (hDv x))
    obtain ⟨θ, hout, hl1, hl2, -, -, hn, hθz⟩ := combine (.refl _) (.refl _) G1 G2 (var z) ζ
    have hθz' : θ z = ζ := by
      rw [hθz]
      split
      · exact (G1.zval ‹_›).resolve_right fun ⟨x, h, _⟩ => hDv x h
      · split
        · exact (G2.zval ‹_›).resolve_right fun ⟨x, h, _⟩ => hDv x h
        · rfl
    refine ⟨var z, θ, ⟨hout, ?_, by simp [subst, hn], fun _ => .inl hθz',
      fun h => (h (occL_append.2 (.inr (.inr (.inl (occ_mk.2 (.inl (show Occ z (var z) from rfl)))))))).elim,
      fun _ => rfl, fun p hp => absurd hp (hDv p),
      fun _ => ⟨imp A1 A2, .hit, (fun p hp => by cases hp), fun hne => ?_⟩⟩⟩
    · intro L hL
      simp only [List.mem_append, List.mem_singleton] at hL
      rcases hL with (hL | hL) | rfl
      · exact hl1 L hL
      · exact hl2 L hL
      · rw [subst_mk]; simp only [subst, hθz', hn, hζz]; exact hTh.mk_refl _ _
    · rcases sh1 with ⟨p, rfl, rfl⟩ | ⟨rfl, h⟩
      · rcases sh2 with ⟨q, rfl, rfl⟩ | ⟨rfl, h⟩
        · exact absurd hD.symm hne
        · exact ⟨_, by rw [hD]; exact .inr rfl, by omega, by omega⟩
      · exact ⟨_, by rw [hD]; exact .inl rfl, by omega, by omega⟩
  · -- the link keeps its shape
    have hx1 : ∀ x, D = var x → n + 1 ≤ x → x < n + 1 + A1.arrows → OccL x L1' a' := by
      intro x hDx hx1 hx2
      rcases down (hx x hDx (by omega) (by omega)) with h | h | h | h
      · exact h
      · rcases loc2 hb' h with e | e | e <;> omega
      · rcases hh' with rfl | ⟨_, rfl⟩ <;> simp only [Occ] at h <;> omega
      · rcases Repl.var_inv hr with rfl | ⟨_, rfl⟩ <;> simp only [Occ] at h <;> omega
    have hx2 : ∀ x, D = var x → n + 1 + A1.arrows ≤ x →
        x < n + 1 + A1.arrows + A2.arrows → OccL x L2' b' := by
      intro x hDx hx1 hx2
      rcases down (hx x hDx (by omega) (by omega)) with h | h | h | h
      · rcases loc1 ha' h with e | e | e <;> omega
      · exact h
      · rcases hh' with rfl | ⟨_, rfl⟩ <;> simp only [Occ] at h <;> omega
      · rcases Repl.var_inv hr with rfl | ⟨_, rfl⟩ <;> simp only [Occ] at h <;> omega
    obtain ⟨B1, θ1, G1⟩ := IH1 a' ha' hx1
    obtain ⟨B2, θ2, G2⟩ := IH2 b' hb' hx2
    -- if `D = n`, nothing below `n` is replaced
    have nfree : D = var n → ¬ OccL z L1' a' ∧ ¬ OccL z L2' b' := fun hDn =>
      ⟨free1 ha' (x := n) (by simp [hDn, Occ]) (by omega) (by omega),
       free2 hb' (x := n) (by simp [hDn, Occ]) (by omega) (by omega)⟩
    rcases hh' with rfl | ⟨hDn, rfl⟩
    · rcases Repl.var_inv hr with rfl | ⟨hDn, rfl⟩
      · -- nothing replaced at this node: `B = B1 → B2`
        obtain ⟨θ, hout, hl1, hl2, hc1, hc2, hn, hθz⟩ :=
          combine ha' hb' G1 G2 (imp B1 B2) ζ
        have hzn : z ≠ n := by omega
        refine ⟨imp B1 B2, θ, ⟨hout, ?_, by simp [subst, hn], ?_, ?_, ?_, ?_, ?_⟩⟩
        · intro L hL
          simp only [List.mem_append, List.mem_singleton] at hL
          rcases hL with (hL | hL) | rfl
          · exact hl1 L hL
          · exact hl2 L hL
          · rw [subst_mk]; simp only [subst, hc1, hc2, hn]; exact hTh.mk_refl _ _
        · intro _
          rw [hθz]
          split
          · exact (G1.zval ‹_›).imp_right fun ⟨x, h, h1, h2⟩ => ⟨x, h, by omega, by omega⟩
          · split
            · exact (G2.zval ‹_›).imp_right fun ⟨x, h, h1, h2⟩ => ⟨x, h, by omega, by omega⟩
            · exact .inl rfl
        · intro h
          rw [G1.nz fun o => h (up1 o), G2.nz fun o => h (up2 o)]
        · intro h
          rcases down h with h | h | h | h
          · exact .inl (G1.zocc h)
          · exact .inr (G2.zocc h)
          · exact absurd h hzn
          · exact absurd h hzn
        · intro p hDp hp h
          have hpn : p ≠ n := by omega
          rcases down h with h | h | h | h
          · exact .inl (G1.pocc p hDp hp h)
          · exact .inr (G2.pocc p hDp hp h)
          · exact absurd h hpn
          · exact absurd h hpn
        · intro h
          have side : ∀ {x}, n + 1 ≤ x ∧ x < n + 1 + A1.arrows ∨
              n + 1 + A1.arrows ≤ x ∧ x < n + 1 + A1.arrows + A2.arrows →
              n ≤ x ∧ x < n + (A1.arrows + A2.arrows + 1) := fun h => by omega
          rcases down h with h | h | h | h
          · obtain ⟨D₁, hR1, hv1, hr1⟩ := G1.d0 h
            by_cases o2 : OccL z L2' b'
            · obtain ⟨D₂, hR2, hv2, hr2⟩ := G2.d0 o2
              have e1 : D₁ = D := Classical.byContradiction fun hne =>
                let ⟨x, hxD, hx1, hx2⟩ := hr1 hne
                free2 hb' hxD (by omega) (by omega) o2
              have e2 : D₂ = D := Classical.byContradiction fun hne =>
                let ⟨x, hxD, hx1, hx2⟩ := hr2 hne
                free1 ha' hxD (by omega) (by omega) h
              rw [e1] at hR1 hv1; rw [e2] at hR2
              exact ⟨D, .imp hR1 hR2, hv1, fun hne => absurd rfl hne⟩
            · rw [G2.nz o2]
              exact ⟨D₁, .imp hR1 (.refl _), hv1, fun hne =>
                let ⟨x, hxD, hx⟩ := hr1 hne; ⟨x, hxD, side (.inl hx)⟩⟩
          · obtain ⟨D₂, hR2, hv2, hr2⟩ := G2.d0 h
            by_cases o1 : OccL z L1' a'
            · obtain ⟨D₁, hR1, hv1, hr1⟩ := G1.d0 o1
              have e1 : D₁ = D := Classical.byContradiction fun hne =>
                let ⟨x, hxD, hx1, hx2⟩ := hr1 hne
                free2 hb' hxD (by omega) (by omega) h
              have e2 : D₂ = D := Classical.byContradiction fun hne =>
                let ⟨x, hxD, hx1, hx2⟩ := hr2 hne
                free1 ha' hxD (by omega) (by omega) o1
              rw [e1] at hR1 hv1; rw [e2] at hR2
              exact ⟨D, .imp hR1 hR2, hv1, fun hne => absurd rfl hne⟩
            · rw [G1.nz o1]
              exact ⟨D₂, .imp (.refl _) hR2, hv2, fun hne =>
                let ⟨x, hxD, hx⟩ := hr2 hne; ⟨x, hxD, side (.inr hx)⟩⟩
          · exact absurd h hzn
          · exact absurd h hzn
      · -- the reading of `n` is replaced: `B = z`
        obtain ⟨o1, o2⟩ := nfree hDn
        obtain ⟨θ, hout, hl1, hl2, hc1, hc2, hn, hθz⟩ :=
          combine ha' hb' G1 G2 (imp B1 B2) ζ
        simp only [o1, o2, ite_false] at hθz
        have hζz : ζ = var z := hζ (hDn ▸ not_isLink_var n)
        refine ⟨var z, θ, ⟨hout, ?_, by simp [subst, hθz, hζz], fun _ => .inl hθz,
          fun h => (h (occL_append.2 (.inr (.inr (.inr (show Occ z (var z) from rfl)))))).elim, fun _ => rfl,
          fun p hp hpN => by rw [hDn] at hp; cases hp; omega,
          fun _ => ⟨imp A1 A2, .hit, (fun p hp => by cases hp),
            fun _ => ⟨n, by simp [hDn, Occ], Nat.le_refl _, by omega⟩⟩⟩⟩
        intro L hL
        simp only [List.mem_append, List.mem_singleton] at hL
        rcases hL with (hL | hL) | rfl
        · exact hl1 L hL
        · exact hl2 L hL
        · rw [subst_mk]; simp only [subst, hc1, hc2, hn]; exact hTh.mk_refl _ _
    · -- the head of the link is replaced: `B = z`, and `z` decodes to `B1 → B2`
      obtain ⟨o1, o2⟩ := nfree hDn
      have hr' : r' = var n := by
        rcases Repl.var_inv hr with h | ⟨_, rfl⟩
        · exact h
        · exfalso
          rcases down (hx n hDn (Nat.le_refl _) (by omega)) with h | h | h | h
          · rcases loc1 ha' h with e | e | e <;> omega
          · rcases loc2 hb' h with e | e | e <;> omega
          · simp only [Occ] at h; omega
          · simp only [Occ] at h; omega
      subst hr'
      obtain ⟨θ, hout, hl1, hl2, hc1, hc2, hn, hθz⟩ :=
        combine ha' hb' G1 G2 (var z) (imp B1 B2)
      simp only [o1, o2, ite_false] at hθz
      refine ⟨var z, θ, ⟨hout, ?_, by simp [subst, hn],
        fun _ => .inr ⟨n, hDn, Nat.le_refl _, by omega⟩,
        fun h => (h (occL_append.2 (.inr (.inr (.inl (occ_mk.2 (.inr (show Occ z (var z) from rfl)))))))).elim,
        fun _ => rfl, fun p hp hpN => by rw [hDn] at hp; cases hp; omega,
        fun _ => ⟨imp A1 A2, .hit, (fun p hp => by cases hp),
          fun _ => ⟨n, by simp [hDn, Occ], Nat.le_refl _, by omega⟩⟩⟩⟩
      intro L hL
      simp only [List.mem_append, List.mem_singleton] at hL
      rcases hL with (hL | hL) | rfl
      · exact hl1 L hL
      · exact hl2 L hL
      · rw [subst_mk]; simp only [subst, hc1, hc2, hθz]; exact hTh.mk_refl _ _

/-- Decoding of a pointwise partial abstraction of the translation. -/
theorem decode (hTh : PreLogic Th) (hζL : IsLink D → Th ζ) (hζ : ¬ IsLink D → ζ = var z) :
    ∀ (A : Form) (pos : Bool) (n : Nat) (Ls' : List Form) (r' : Form),
      (∀ q, Occ q A → q < N) → N ≤ n → n + A.arrows ≤ z →
      Pw (Repl D z) (tr A pos n).2 Ls' → Repl D z (tr A pos n).1 r' →
      (∀ x, D = var x → n ≤ x → x < n + A.arrows → OccL x Ls' r') →
      ∃ B θ, Good D z N ζ Th n A Ls' r' B θ
  | var p, pos, n, Ls', r', hA, hN, hz, hL, hr, _ => by
      have hp : p < N := hA p rfl
      simp only [tr] at hL hr
      simp only [arrows] at hz
      cases hL
      have hOcc : ∀ {q}, OccL q [] r' → Occ q r' := fun h =>
        h.elim (fun ⟨_, h, _⟩ => absurd h (List.not_mem_nil)) id
      rcases Repl.var_inv hr with rfl | ⟨hD, rfl⟩
      · refine ⟨var p, var, ⟨fun _ _ _ => rfl, by simp, subst_var _, ?_, fun _ => rfl,
          ?_, fun _ _ _ h => hOcc h, ?_⟩⟩ <;>
        · intro h; have h := hOcc h; simp only [Occ] at h; omega
      · refine ⟨var z, var, ⟨fun _ _ _ => rfl, by simp, rfl,
          fun _ => .inl (hζ (hD ▸ not_isLink_var p)).symm,
          fun h => absurd (.inr rfl) h, fun _ => rfl, ?_,
          fun _ => ⟨var p, .hit, fun q hq => by cases hq; exact ⟨hD.symm, hp⟩,
            fun h => absurd hD.symm h⟩⟩⟩
        intro q _ hq h; have h := hOcc h; simp only [Occ] at h; omega
  | imp A1 A2, pos, n, Ls', r', hA, hN, hz, hL, hr, hx => by
      simp only [tr] at hL hr
      obtain ⟨L12, LE, rfl, h12, hE⟩ := Pw.append_inv hL
      obtain ⟨L1', L2', rfl, h1, h2⟩ := Pw.append_inv h12
      obtain ⟨E', rfl, hE'⟩ := Pw.single_inv hE
      simp only [arrows] at hz hx
      have hA1 : ∀ q, Occ q A1 → q < N := fun q h => hA q (.inl h)
      have hA2 : ∀ q, Occ q A2 → q < N := fun q h => hA q (.inr h)
      have sh : ∀ (C : Form) (pos : Bool) (m : Nat),
          (∃ p, C = var p ∧ (tr C pos m).1 = var p) ∨ ((tr C pos m).1 = var m ∧ 0 < C.arrows) :=
        tr_fst
      exact decode_node hTh hζL hζ hA hN hz
        (fun L hL q hq => occ_tr_snd L hL hq) (fun q hq => occ_tr_fst hq) (sh A1 (!pos) (n + 1))
        (fun L hL q hq => occ_tr_snd L hL hq) (fun q hq => occ_tr_fst hq)
        (sh A2 pos (n + 1 + A1.arrows)) h1 h2 hE' hr hx
        (fun c1 hc1 hx1 => decode hTh hζL hζ A1 (!pos) (n + 1) L1' c1 hA1 (by omega) (by omega) h1 hc1 hx1)
        (fun c2 hc2 hx2 =>
          decode hTh hζL hζ A2 pos (n + 1 + A1.arrows) L2' c2 hA2 (by omega) (by omega) h2 hc2 hx2)

end DecodeProof

/-! ## Main theorem -/

section Main
open Form Classical

theorem Pw.eq_self {D : Form} {z : Nat} :
    ∀ {l l' : List Form}, Pw (Repl D z) l l' → (∀ L ∈ l, ∀ L', Repl D z L L' → L' = L) → l' = l
  | _, _, .nil, _ => rfl
  | _, _, .cons ha h, hl => by
      rw [hl _ List.mem_cons_self _ ha,
        h.eq_self (fun L hL => hl L (List.mem_cons_of_mem _ hL))]

theorem Pw.refl {D : Form} {z : Nat} : ∀ l : List Form, Pw (Repl D z) l l
  | [] => .nil
  | _ :: l => .cons (.refl _) (Pw.refl l)

/-- **Main theorem.** For every logic `Th` (closed under substitution and
modus ponens, proving `γ → γ`, consistent), the polarized Statman
translation preserves minimality in `Th`, provided `statman A N ∈ Th`.
Here `N` bounds the variables of `A`, and the fresh variables are
`N, N+1, …`. -/
theorem statman_minimalIn {Th : Form → Prop} (hTh : Logic Th) {A : Form} {N : Nat}
    (hN : ∀ q, Occ q A → q < N) (hA : MinimalIn Th A) (hS : Th (statman A N)) :
    MinimalIn Th (statman A N) := by
  apply reduction hTh (N + A.arrows) hS
  intro D z α' hzb _ hR hz' hp hV
  have hzA : ¬ Occ z A := fun h => by have := hN z h; omega
  rcases chain_repl hR with ⟨Ls', r', rfl, hL, hr⟩ | ⟨L, Ls₁, Ls₂, Ls₁', e, hD, rfl, h1⟩
  · -- pointwise abstraction: decode it to a proper abstraction of `A`
    let ζ : Form := if IsLink D then imp (var z) (var z) else var z
    have hζL : IsLink D → Th ζ := fun h => by simp only [ζ, h, ite_true]; exact hTh.refl _
    have hζ : ¬ IsLink D → ζ = var z := fun h => by simp [ζ, h]
    have hloc : ∀ {q}, Occ q (chain Ls' r') → OccL q Ls' r' := fun h => occ_chain.1 h
    obtain ⟨B, θ, G⟩ := decode hTh.toPreLogic hζL hζ A true N Ls' r' hN (Nat.le_refl _) hzb hL hr
      (fun x hx _ _ => hloc (hp x hx))
    have hB : Th B := by
      have := hTh.subst hV θ
      rw [subst_chain] at this
      rw [← G.rep]
      exact hTh.of_chain this fun L hL =>
        let ⟨L0, hL0, e⟩ := List.mem_map.1 hL; e ▸ G.links L0 hL0
    obtain ⟨D₀, hR0, hv0, -⟩ := G.d0 (hloc hz')
    exact strict hA hR0 hzA (G.zocc (hloc hz')) (fun p hp0 =>
      have ⟨e, hpN⟩ := hv0 p hp0
      ⟨by omega, G.pocc p (hp0 ▸ e).symm hpN (hloc (hp p (hp0 ▸ e).symm))⟩) hB
  · -- a tail is replaced: the remaining links decode to `γ → γ`, leaving `z`
    have hleaf : ∀ L ∈ (tr A true N).2, L.leaves = 3 := leaves_tr_snd
    have hDl : 3 < D.leaves := by
      rw [hD]; simp only [chain, leaves]
      have := hleaf L (by rw [e]; simp); have := leaves_pos (chain Ls₂ (tr A true N).1); omega
    have hLs : Ls₁' = Ls₁ := h1.eq_self fun L hL L' hR =>
      hR.eq_of_leaves (by rw [hleaf L (by rw [e]; simp [hL])]; exact hDl)
    subst hLs
    obtain ⟨B, θ, G⟩ := decode (D := var z) (N := N) (ζ := var z) hTh.toPreLogic
      (fun h => absurd h (not_isLink_var z)) (fun _ => rfl) A true N _ _ hN (Nat.le_refl _) hzb
      (Pw.refl _) (.refl _) (fun x hx _ _ => by cases hx; omega)
    let θ' : Nat → Form := fun q => if q = z then var z else θ q
    have hθ' : ∀ L ∈ (tr A true N).2, Th (L.subst θ') := fun L hL => by
      rw [subst_congr L (θ' := θ) fun q hq => by
        have : q ≠ z := by
          rcases occ_tr_snd L hL hq with h | h
          · have := hN q h; omega
          · omega
        simp [θ', this]]
      exact G.links L hL
    have := hTh.subst hV θ'
    rw [subst_chain] at this
    have hz := hTh.of_chain this fun L hL =>
      let ⟨L0, hL0, e'⟩ := List.mem_map.1 hL
      e' ▸ hθ' L0 (by rw [e]; simp [hL0])
    simp only [subst, θ', ite_true] at hz
    exact hTh.cons z hz

/-- Classical validity is a logic in the above sense. -/
theorem logic_valid : Logic Valid where
  subst h θ := valid_subst h θ
  mp h ha v := by have := h v; simp only [eval, ha v] at this; simpa using this
  refl g v := by simp only [eval]; cases g.eval v <;> rfl
  cons p h := by have := h (fun _ => false); simp [eval] at this

/-- **Main theorem, classical case.** The polarized Statman translation
preserves minimality in classical logic. -/
theorem statman_minimal {A : Form} {N : Nat} (hN : ∀ q, Occ q A → q < N)
    (hA : Minimal A) : Minimal (statman A N) :=
  statman_minimalIn logic_valid hN hA (statman_valid hA.1 N)

end Main

/-! ## Order bound -/

section Order
open Form

/-- Order: `Ord p = 1`, `Ord (a → b) = max (Ord a + 1) (Ord b)`. -/
def ord : Form → Nat
  | var _   => 1
  | imp a b => max (ord a + 1) (ord b)

theorem ord_tr_snd : ∀ {A : Form} {pos : Bool} {n : Nat}, ∀ L ∈ (tr A pos n).2, ord L ≤ 3
  | var p, pos, n, L, hL => by simp [tr] at hL
  | imp A B, pos, n, L, hL => by
      simp only [tr, List.mem_append, List.mem_singleton] at hL
      rcases hL with (hL | hL) | rfl
      · exact ord_tr_snd L hL
      · exact ord_tr_snd L hL
      · rcases tr_fst A (!pos) (n + 1) with ⟨_, _, ea⟩ | ⟨ea, _⟩ <;>
        rcases tr_fst B pos (n + 1 + A.arrows) with ⟨_, _, eb⟩ | ⟨eb, _⟩ <;>
        · rw [ea, eb]; cases pos <;> simp [mk, ord]

theorem ord_chain (r : Form) (hr : ord r ≤ 4) :
    ∀ Ls : List Form, (∀ L ∈ Ls, ord L ≤ 3) → ord (chain Ls r) ≤ 4
  | [], _ => hr
  | L :: Ls, h => by
      have := h L List.mem_cons_self
      have := ord_chain r hr Ls fun L hL => h L (List.mem_cons_of_mem _ hL)
      simp only [chain, ord]; omega

/-- The translation has order at most four. -/
theorem statman_ord (A : Form) (n : Nat) : ord (statman A n) ≤ 4 :=
  ord_chain _ (by rcases tr_fst A true n with ⟨_, _, e⟩ | ⟨e, _⟩ <;> rw [e] <;> simp [ord])
    _ fun L hL => ord_tr_snd L hL

end Order

/-! ## Soundness over `BCI`, and `L + A = L + statman A N`

`BCIExt Th`: `Th` is closed under substitution and modus ponens and proves
all instances of `B`, `C`, `I`. These are exactly the implicational logics
containing `BCI` (the implicational fragment of `FLe`), e.g. `BCK`, `IL`,
`LC`, `CL`. -/

section BCI
open Form

local infixr:55 " ⟶ " => Form.imp

structure BCIExt (Th : Form → Prop) : Prop extends PreLogic Th where
  axB : ∀ a b c, Th ((b ⟶ c) ⟶ (a ⟶ b) ⟶ a ⟶ c)
  axC : ∀ a b c, Th ((a ⟶ b ⟶ c) ⟶ b ⟶ a ⟶ c)

variable {Th : Form → Prop} (hTh : BCIExt Th)
include hTh

theorem BCIExt.comp {a b c : Form} (h1 : Th (a ⟶ b)) (h2 : Th (b ⟶ c)) : Th (a ⟶ c) :=
  hTh.mp (hTh.mp (hTh.axB a b c) h2) h1

theorem BCIExt.perm {a b c : Form} (h : Th (a ⟶ b ⟶ c)) : Th (b ⟶ a ⟶ c) :=
  hTh.mp (hTh.axC a b c) h

/-- `(b → c) → Γ ⇒ b → Γ ⇒ c`, where `Γ ⇒ x` is `chain Γ x`. -/
theorem BCIExt.lift_thm (b c : Form) :
    ∀ Γ : List Form, Th ((b ⟶ c) ⟶ chain Γ b ⟶ chain Γ c)
  | [] => hTh.refl _
  | g :: Γ => hTh.comp (BCIExt.lift_thm b c Γ) (hTh.axB g _ _)

theorem BCIExt.lift {b c : Form} (Γ : List Form) (h : Th (b ⟶ c)) (hb : Th (chain Γ b)) :
    Th (chain Γ c) :=
  hTh.mp (hTh.mp (hTh.lift_thm b c Γ) h) hb

/-- `Γ₁ ⇒ (b → c) → Γ₂ ⇒ b → Γ₁ ⇒ Γ₂ ⇒ c`. -/
theorem BCIExt.join_thm (b c : Form) (Γ₂ : List Form) :
    ∀ Γ₁ : List Form, Th (chain Γ₁ (b ⟶ c) ⟶ chain Γ₂ b ⟶ chain Γ₁ (chain Γ₂ c))
  | [] => hTh.lift_thm b c Γ₂
  | g :: Γ₁ =>
      hTh.comp (hTh.mp (hTh.lift_thm _ _ [g]) (BCIExt.join_thm b c Γ₂ Γ₁)) (hTh.axC g _ _)

/-- `Γ ⇒ (a → b) → a → Γ ⇒ b`. -/
theorem BCIExt.pull_thm (a b : Form) :
    ∀ Γ : List Form, Th (chain Γ (a ⟶ b) ⟶ a ⟶ chain Γ b)
  | [] => hTh.refl _
  | g :: Γ =>
      hTh.comp (hTh.mp (hTh.lift_thm _ _ [g]) (BCIExt.pull_thm a b Γ)) (hTh.axC g _ _)

theorem BCIExt.compose2 {a f z p r : Form} (ha : Th (a ⟶ f ⟶ z)) (hp : Th (p ⟶ z ⟶ r)) :
    Th (a ⟶ p ⟶ f ⟶ r) :=
  hTh.comp ha (hTh.perm (hTh.comp hp (hTh.axB f z r)))

omit hTh in
theorem chain_append (r : Form) :
    ∀ l₁ l₂ : List Form, chain (l₁ ++ l₂) r = chain l₁ (chain l₂ r)
  | [], _ => rfl
  | _ :: l₁, l₂ => by simp [chain, chain_append r l₁ l₂]

/-- The combinator for one link, in both polarities. -/
theorem BCIExt.link (pos : Bool) (A B a b : Form) (x : Nat) :
    Th (StatmanMin.mk (!pos) A a ⟶ StatmanMin.mk pos B b ⟶
      StatmanMin.mk pos (a ⟶ b) (var x) ⟶ StatmanMin.mk pos (A ⟶ B) (var x)) := by
  cases pos
  · -- negative: (A → a) → (b → B) → (x → a → b) → x → A → B
    exact hTh.lift [_, _] (hTh.axB (var x) (a ⟶ b) (A ⟶ B))
      (hTh.compose2 (hTh.perm (hTh.axB A a b)) (hTh.axB A b B))
  · -- positive: (a → A) → (B → b) → ((a → b) → x) → (A → B) → x
    exact hTh.lift [_, _] (hTh.perm (hTh.axB (A ⟶ B) (a ⟶ b) (var x)))
      (hTh.compose2 (hTh.perm (hTh.axB a A B)) (hTh.axB a B b))

/-- Soundness, node by node: `links ⇒ (A → rep)` at positive and
`links ⇒ (rep → A)` at negative occurrences. Each link is used once. -/
theorem BCIExt.tr_sound :
    ∀ (A : Form) (pos : Bool) (n : Nat),
      Th (chain (tr A pos n).2 (StatmanMin.mk pos A (tr A pos n).1))
  | var p, pos, n => hTh.mk_refl pos (var p)
  | imp A B, pos, n => by
      simp only [tr, chain_append]
      have h1 := BCIExt.tr_sound A (!pos) (n + 1)
      have h2 := BCIExt.tr_sound B pos (n + 1 + A.arrows)
      have h12 := hTh.lift _
        (hTh.link pos A B (tr A (!pos) (n + 1)).1 (tr B pos (n + 1 + A.arrows)).1 n) h1
      exact hTh.mp (hTh.mp (hTh.join_thm _ _ _ _) h12) h2

/-- `BCI ⊢ A → statman A N`. -/
theorem BCIExt.statman_imp (A : Form) (N : Nat) : Th (A ⟶ statman A N) :=
  hTh.mp (hTh.pull_thm _ _ _) (hTh.tr_sound A true N)

omit hTh in
/-- Decoding: every `PreLogic` containing `statman A N` contains `A`. -/
theorem PreLogic.of_statman (hP : PreLogic Th) {A : Form} {N : Nat}
    (hN : ∀ q, Occ q A → q < N) (hS : Th (statman A N)) : Th A := by
  let z := N + A.arrows
  obtain ⟨B, θ, G⟩ := decode (D := var z) (N := N) (ζ := var z) hP
    (fun h => absurd h (not_isLink_var z)) (fun _ => rfl) A true N _ _ hN (Nat.le_refl _)
    (Nat.le_refl _) (Pw.refl _) (.refl _) (fun x hx _ _ => by cases hx; omega)
  have hz : ¬ OccL z (tr A true N).2 (tr A true N).1 := by
    rintro (⟨L, hL, h⟩ | h)
    · rcases occ_tr_snd L hL h with h | h
      · have := hN z h; omega
      · omega
    · rcases occ_tr_fst h with h | h
      · have := hN z h; omega
      · omega
  have := hP.subst hS θ
  rw [statman, subst_chain] at this
  have := hP.of_chain this fun L hL =>
    let ⟨L0, hL0, e⟩ := List.mem_map.1 hL; e ▸ G.links L0 hL0
  rwa [G.rep, G.nz hz] at this

/-- Every implicational logic containing `BCI` contains `A` iff it contains
`statman A N`. Hence `L + A = L + statman A N` for every `L ⊇ BCI`. -/
theorem BCIExt.statman_iff {A : Form} {N : Nat} (hN : ∀ q, Occ q A → q < N) :
    Th A ↔ Th (statman A N) :=
  ⟨fun h => hTh.mp (hTh.statman_imp A N) h, hTh.toPreLogic.of_statman hN⟩

/-- **Main theorem over `BCI`.** For every consistent implicational logic
`Th ⊇ BCI` (e.g. `BCI`, `BCK`, `IL`, `LC`, `CL`), the translation preserves
minimality in `Th`. -/
theorem BCIExt.statman_minimal (hc : ∀ p, ¬ Th (var p)) {A : Form} {N : Nat}
    (hN : ∀ q, Occ q A → q < N) (hA : MinimalIn Th A) : MinimalIn Th (statman A N) :=
  statman_minimalIn { hTh.toPreLogic with cons := hc } hN hA
    ((hTh.statman_iff hN).1 hA.1)

end BCI

/-! ## The concrete formula `S(G')`

Variables `0,…,7` are `a, a', b', b, c'', c', c''', c`; the extension
variable `x_i` of the paper is `7 + i`. -/

section Gprime
open Form

local infixr:55 " ⟶ " => Form.imp
local notation "V" => Form.var

/-- The formula `G'` of Nakamura–Matsuda (2021). -/
def Gprime : Form :=
  (V 0 ⟶ V 1) ⟶ (V 2 ⟶ V 3) ⟶ (V 4 ⟶ V 5) ⟶ (V 6 ⟶ V 5) ⟶
  ((V 0 ⟶ V 3) ⟶ V 4) ⟶ ((V 2 ⟶ V 1) ⟶ V 6) ⟶
  (((V 1 ⟶ V 2) ⟶ V 4) ⟶ ((V 3 ⟶ V 0) ⟶ V 6) ⟶ V 5 ⟶ V 7) ⟶ V 7

/-- `S(G')` written out, as displayed in the paper (Corollary 5.3). -/
def SGprime : Form :=
  (V 9 ⟶ (V 0 ⟶ V 1)) ⟶
  (V 11 ⟶ (V 2 ⟶ V 3)) ⟶
  (V 13 ⟶ (V 4 ⟶ V 5)) ⟶
  (V 15 ⟶ (V 6 ⟶ V 5)) ⟶
  ((V 0 ⟶ V 3) ⟶ V 18) ⟶
  (V 17 ⟶ (V 18 ⟶ V 4)) ⟶
  ((V 2 ⟶ V 1) ⟶ V 21) ⟶
  (V 20 ⟶ (V 21 ⟶ V 6)) ⟶
  (V 25 ⟶ (V 1 ⟶ V 2)) ⟶
  ((V 25 ⟶ V 4) ⟶ V 24) ⟶
  (V 28 ⟶ (V 3 ⟶ V 0)) ⟶
  ((V 28 ⟶ V 6) ⟶ V 27) ⟶
  (V 29 ⟶ (V 5 ⟶ V 7)) ⟶
  (V 26 ⟶ (V 27 ⟶ V 29)) ⟶
  (V 23 ⟶ (V 24 ⟶ V 26)) ⟶
  ((V 23 ⟶ V 7) ⟶ V 22) ⟶
  ((V 20 ⟶ V 22) ⟶ V 19) ⟶
  ((V 17 ⟶ V 19) ⟶ V 16) ⟶
  ((V 15 ⟶ V 16) ⟶ V 14) ⟶
  ((V 13 ⟶ V 14) ⟶ V 12) ⟶
  ((V 11 ⟶ V 12) ⟶ V 10) ⟶
  ((V 9 ⟶ V 10) ⟶ V 8) ⟶
  V 8

theorem statman_Gprime : statman Gprime 8 = SGprime := by decide

theorem SGprime_ord : ord SGprime = 4 := by decide

end Gprime

end StatmanMin
