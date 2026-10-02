import SGprime.Defs

/-!
# Lemmas

This file need not be read: it is checked by Lean.  It defines no notation.

## Method

*Logics.*  Derivations are written as simply typed λ-terms (`Tm`) and
checked by a small type checker `infer`, which is proved sound with respect
to the Hilbert system via the deduction theorem.  The two inclusions need
only two concrete terms: `S(G') ∈ LC` and `LCax ∈ IL ⊕ S(G')`.

*Minimality.*  Suppose `β` is valid and `σ β = S(G')`.  For a variable `y`
of `β`, the formula `σ[y ↦ z] β`, with `z` fresh, is valid and is obtained
from `S(G')` by replacing some occurrences of the formula `σ y` by `z`
(`repl_of_subst`).  It suffices therefore to refute all such replacements
in which `z` actually occurs and either `σ y` is compound or `σ y` is a
variable `p` that still occurs.  These are finitely many (`cands`), and each
of them has an explicit Boolean countermodel (`masks`), checked by kernel
evaluation.  If no such `y` exists, `σ` maps the variables of `β`
injectively to variables, so `β` is a renaming of `S(G')`.
-/

namespace SGprimeDirect

open Form

/-! ## Basic lemmas -/

def Occ (q : Nat) : Form → Prop
  | var p => p = q
  | imp a b => Occ q a ∨ Occ q b


def Form.beq : Form → Form → Bool
  | var p, var q => Nat.beq p q
  | imp a b, imp c d => Form.beq a c && Form.beq b d
  | _, _ => false

theorem Form.eq_of_beq : ∀ {a b : Form}, Form.beq a b = true → a = b
  | var p, var q, h => by
      simp only [Form.beq] at h
      rw [Nat.eq_of_beq_eq_true h]
  | imp a b, imp c d, h => by
      simp only [Form.beq, Bool.and_eq_true] at h
      rw [Form.eq_of_beq h.1, Form.eq_of_beq h.2]
  | var _, imp _ _, h => by simp [Form.beq] at h
  | imp _ _, var _, h => by simp [Form.beq] at h

theorem Form.beq_refl : ∀ a : Form, Form.beq a a = true
  | var p => by simp [Form.beq]
  | imp a b => by simp [Form.beq, Form.beq_refl a, Form.beq_refl b]

def occB (q : Nat) : Form → Bool
  | var p => Nat.beq p q
  | imp a b => occB q a || occB q b

theorem occB_iff {q : Nat} : ∀ {t : Form}, occB q t = true ↔ Occ q t
  | var p => by simp [occB, Occ]
  | imp a b => by simp [occB, Occ, occB_iff]

theorem eval_subst (v : Nat → Bool) (σ : Nat → Form) :
    ∀ t : Form, eval v (subst σ t) = eval (fun p => eval v (σ p)) t
  | var _ => rfl
  | imp a b => by simp only [subst, eval, eval_subst v σ a, eval_subst v σ b]

theorem valid_subst {t : Form} (h : Valid t) (σ : Nat → Form) :
    Valid (subst σ t) := fun v => by rw [eval_subst]; exact h _

theorem subst_subst (σ τ : Nat → Form) :
    ∀ t : Form, subst τ (subst σ t) = subst (fun p => subst τ (σ p)) t
  | var _ => rfl
  | imp a b => by simp only [subst, subst_subst σ τ a, subst_subst σ τ b]

theorem occ_subst {σ : Nat → Form} {x q : Nat} :
    ∀ {t : Form}, Occ x t → Occ q (σ x) → Occ q (subst σ t)
  | var p, hx, hq => by simp only [Occ] at hx; subst hx; exact hq
  | imp _ _, hx, hq => by
      rcases hx with hx | hx
      · exact Or.inl (occ_subst hx hq)
      · exact Or.inr (occ_subst hx hq)

/-! ## Derivations with hypotheses -/

/-- Derivations from hypotheses `Γ` in `IL ⊕ Ax`. -/
inductive Der (Ax : List Form) (Γ : List Form) : Form → Prop
  | k (a b : Form) : Der Ax Γ (axK a b)
  | s (a b c : Form) : Der Ax Γ (axS a b c)
  | ax {B : Form} (h : B ∈ Ax) (σ : Nat → Form) : Der Ax Γ (subst σ B)
  | hyp {a : Form} (h : a ∈ Γ) : Der Ax Γ a
  | mp {a b : Form} : Der Ax Γ (a ⟶ b) → Der Ax Γ a → Der Ax Γ b

/-- Derivability without hypotheses; it coincides with `ThmD` (`thm_iff`). -/
def ThmD (Ax : List Form) (φ : Form) : Prop := Der Ax [] φ

theorem Der.id {Ax Γ : List Form} (a : Form) : Der Ax Γ (a ⟶ a) :=
  .mp (.mp (.s a (a ⟶ a) a) (.k a (a ⟶ a))) (.k a a)

theorem Der.deduction {Ax Γ : List Form} {a b : Form}
    (h : Der Ax (a :: Γ) b) : Der Ax Γ (a ⟶ b) := by
  induction h with
  | k x y => exact .mp (.k _ a) (.k x y)
  | s x y w => exact .mp (.k _ a) (.s x y w)
  | ax hB σ => exact .mp (.k _ a) (.ax hB σ)
  | hyp h =>
      rcases List.mem_cons.1 h with h | h
      · subst h; exact Der.id _
      · exact .mp (.k _ a) (.hyp h)
  | mp _ _ ih1 ih2 => exact .mp (.mp (.s _ _ _) ih1) ih2

theorem ThmD.subst {Ax : List Form} {φ : Form} (h : ThmD Ax φ) (τ : Nat → Form) :
    ThmD Ax (subst τ φ) := by
  unfold ThmD at *
  induction h with
  | k a b => exact .k _ _
  | s a b c => exact .s _ _ _
  | ax hB σ => rw [subst_subst]; exact .ax hB _
  | hyp h => cases h
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

/-- If every axiom of `Ax` is a theorem of `IL ⊕ Ax'`, then
`IL ⊕ Ax ⊆ IL ⊕ Ax'`. -/
theorem ThmD.transfer {Ax Ax' : List Form} (hAx : ∀ B ∈ Ax, ThmD Ax' B)
    {φ : Form} (h : ThmD Ax φ) : ThmD Ax' φ := by
  unfold ThmD at *
  induction h with
  | k a b => exact .k _ _
  | s a b c => exact .s _ _ _
  | ax hB σ => exact ThmD.subst (hAx _ hB) σ
  | hyp h => cases h
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

theorem ThmD.valid {Ax : List Form} (hAx : ∀ B ∈ Ax, Valid B) {φ : Form}
    (h : ThmD Ax φ) : Valid φ := by
  unfold ThmD at h
  induction h with
  | k a b => intro v; simp only [axK, eval]; cases eval v a <;> cases eval v b <;> rfl
  | s a b c =>
      intro v; simp only [axS, eval]
      cases eval v a <;> cases eval v b <;> cases eval v c <;> rfl
  | ax hB σ => exact valid_subst (hAx _ hB) σ
  | hyp h => cases h
  | mp _ _ ih1 ih2 =>
      intro v; have h1 := ih1 v; have h2 := ih2 v
      simp only [eval, h2, Bool.not_true, Bool.false_or] at h1; exact h1

/-! ## A certified checker for λ-terms -/

/-- Simply typed λ-terms with named variables; `ax i σ` is the instance
of the `i`-th extra axiom under the substitution given by the list `σ`. -/
inductive Tm where
  | hyp : Nat → Tm
  | lam : Nat → Form → Tm → Tm
  | app : Tm → Tm → Tm
  | ax  : Nat → List (Nat × Form) → Tm

def lookupF (n : Nat) : List (Nat × Form) → Option Form
  | [] => none
  | (m, A) :: Γ => if Nat.beq n m then some A else lookupF n Γ

def sigmaOf (σ : List (Nat × Form)) (p : Nat) : Form := (lookupF p σ).getD (var p)

def nthF : List Form → Nat → Option Form
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => nthF l n

def appF : Option Form → Option Form → Option Form
  | some (imp A B), some A' => if Form.beq A A' then some B else none
  | _, _ => none

def infer (Ax : List Form) : List (Nat × Form) → Tm → Option Form
  | Γ, .hyp n => lookupF n Γ
  | Γ, .lam n A t => (infer Ax ((n, A) :: Γ) t).map (imp A)
  | Γ, .app t u => appF (infer Ax Γ t) (infer Ax Γ u)
  | _, .ax i σ => (nthF Ax i).map (subst (sigmaOf σ))

/-- `proves Ax t φ` checks that the closed term `t` has type `φ`. -/
def proves (Ax : List Form) (t : Tm) (φ : Form) : Bool :=
  match infer Ax [] t with
  | some ψ => Form.beq ψ φ
  | none => false

theorem lookupF_mem {n : Nat} {A : Form} :
    ∀ {Γ : List (Nat × Form)}, lookupF n Γ = some A → A ∈ Γ.map Prod.snd
  | [], h => by simp [lookupF] at h
  | (m, B) :: Γ, h => by
      simp only [lookupF] at h
      split at h
      · cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lookupF_mem h)

theorem nthF_mem {A : Form} : ∀ {l : List Form} {n : Nat}, nthF l n = some A → A ∈ l
  | [], _, h => by simp [nthF] at h
  | a :: _, 0, h => by simp only [nthF, Option.some.injEq] at h; subst h; exact List.mem_cons_self ..
  | _ :: l, n + 1, h => List.mem_cons_of_mem _ (nthF_mem (l := l) (n := n) h)

theorem appF_some : ∀ {o1 o2 : Option Form} {φ : Form},
    appF o1 o2 = some φ → ∃ A, o1 = some (A ⟶ φ) ∧ o2 = some A
  | none, _, _, h => by simp [appF] at h
  | some (var _), _, _, h => by simp [appF] at h
  | some (imp _ _), none, _, h => by simp [appF] at h
  | some (imp A B), some A', φ, h => by
      simp only [appF] at h
      split at h
      · rename_i hb
        cases h
        exact ⟨A, rfl, by rw [Form.eq_of_beq hb]⟩
      · cases h

theorem map_some {f : Form → Form} : ∀ {o : Option Form} {φ : Form},
    o.map f = some φ → ∃ ψ, o = some ψ ∧ φ = f ψ
  | none, _, h => by cases h
  | some ψ, _, h => by cases h; exact ⟨ψ, rfl, rfl⟩

theorem infer_sound (Ax : List Form) :
    ∀ (t : Tm) (Γ : List (Nat × Form)) (φ : Form),
      infer Ax Γ t = some φ → Der Ax (Γ.map Prod.snd) φ
  | .hyp _, _, _, h => .hyp (lookupF_mem h)
  | .lam n A t, Γ, _, h => by
      obtain ⟨ψ, h1, rfl⟩ := map_some h
      exact Der.deduction (infer_sound Ax t ((n, A) :: Γ) ψ h1)
  | .app t u, Γ, φ, h => by
      obtain ⟨A, h1, h2⟩ := appF_some h
      exact .mp (infer_sound Ax t Γ _ h1) (infer_sound Ax u Γ _ h2)
  | .ax _ _, _, _, h => by
      obtain ⟨B, h1, rfl⟩ := map_some h
      exact .ax (nthF_mem h1) _

theorem ThmD.of_proves {Ax : List Form} {t : Tm} {φ : Form}
    (h : proves Ax t φ = true) : ThmD Ax φ := by
  unfold proves at h
  split at h
  · rename_i ψ hψ
    rw [← Form.eq_of_beq h]
    exact infer_sound Ax t [] ψ hψ
  · cases h

/-! ## The formula `G'` and the translation -/

/-- The formula `G'` of Nakamura and Matsuda. -/
def Gprime : Form :=
  (V 0 ⟶ V 1) ⟶ (V 2 ⟶ V 3) ⟶ (V 4 ⟶ V 5) ⟶ (V 6 ⟶ V 5) ⟶
  ((V 0 ⟶ V 3) ⟶ V 4) ⟶ ((V 2 ⟶ V 1) ⟶ V 6) ⟶
  (((V 1 ⟶ V 2) ⟶ V 4) ⟶ ((V 3 ⟶ V 0) ⟶ V 6) ⟶ V 5 ⟶ V 7) ⟶ V 7

/-! ### The translation, used only to generate certificates

`trans f pos n` follows Definition `def:S`: it returns the representative of
`f`, the defining premises (named by their extension variable, in
post-order), the pairs `(n, f_u)` recording the subformula `f_u` named by
`x_u = V n`, the next fresh index, and a function that turns a proof of `f`
into a proof of the representative (if `pos`) or a proof of the
representative into a proof of `f` (otherwise), as in Lemma `lem:sound`. -/

structure Tr where
  rep : Form
  links : List (Nat × Form)
  defs : List (Nat × Form)
  next : Nat
  conv : Tm → Tm

def trans : Form → Bool → Nat → Tr
  | var p, _, n => ⟨var p, [], [], n, id⟩
  | imp A B, pos, n =>
      let tA := trans A (!pos) (n + 1)
      let tB := trans B pos tA.next
      let body := tA.rep ⟶ tB.rep
      let link := if pos then body ⟶ V n else V n ⟶ body
      let conv : Tm → Tm :=
        if pos then
          fun t => .app (.hyp n)
            (.lam (100 + n) tA.rep (tB.conv (.app t (tA.conv (.hyp (100 + n))))))
        else
          fun t => .lam (200 + n) A
            (tB.conv (.app (.app (.hyp n) t) (tA.conv (.hyp (200 + n)))))
      ⟨V n, tA.links ++ tB.links ++ [(n, link)], tA.defs ++ tB.defs ++ [(n, imp A B)],
        tB.next, conv⟩

def chain : List Form → Form → Form
  | [], r => r
  | a :: l, r => a ⟶ chain l r

def TG : Tr := trans Gprime true 8

/-- The displayed formula is indeed `S(G')`. -/
theorem SG_eq_translation : Form.beq (chain (TG.links.map Prod.snd) TG.rep) SG = true := by
  decide +kernel

/-! ## `IL ⊕ S(G') = LC` -/

/-- A proof of `G'` in `LC`; `LCax` is extra axiom number `0`. -/
def proofG : Tm :=
  .lam 301 (V 0 ⟶ V 1) <| .lam 302 (V 2 ⟶ V 3) <| .lam 303 (V 4 ⟶ V 5) <|
  .lam 304 (V 6 ⟶ V 5) <| .lam 305 ((V 0 ⟶ V 3) ⟶ V 4) <|
  .lam 306 ((V 2 ⟶ V 1) ⟶ V 6) <|
  .lam 307 (((V 1 ⟶ V 2) ⟶ V 4) ⟶ ((V 3 ⟶ V 0) ⟶ V 6) ⟶ V 5 ⟶ V 7) <|
  -- from `a' → b'` obtain `a → b`, hence `c''`
  let A1 := .lam 310 (V 1 ⟶ V 2) (.app (.hyp 305)
    (.lam 311 (V 0) (.app (.hyp 302) (.app (.hyp 310) (.app (.hyp 301) (.hyp 311))))))
  -- from `b → a` obtain `b' → a'`, hence `c'''`
  let A2 := .lam 312 (V 3 ⟶ V 0) (.app (.hyp 306)
    (.lam 313 (V 2) (.app (.hyp 301) (.app (.hyp 312) (.app (.hyp 302) (.hyp 313))))))
  -- `c'` by the instance `((a → b) → c') → ((b → a) → c') → c'` of `LCax`
  let C := .app (.app (.ax 0 [(0, V 0), (1, V 3), (2, V 5)])
      (.lam 314 (V 0 ⟶ V 3) (.app (.hyp 303) (.app (.hyp 305) (.hyp 314)))))
    (.lam 315 (V 3 ⟶ V 0) (.app (.hyp 304) (.app (.hyp 306)
      (.lam 316 (V 2) (.app (.hyp 301) (.app (.hyp 315) (.app (.hyp 302) (.hyp 316))))))))
  .app (.app (.app (.hyp 307) A1) A2) C

/-- A proof of `S(G')` in `LC`: assume the defining premises and convert
the proof of `G'` into a proof of `x_ε`. -/
def proofSG : Tm :=
  TG.links.foldr (fun (n, L) t => .lam n L t) (TG.conv proofG)

/-- The substitution `a, a' ↦ a`, `b, b' ↦ b`, `c, c', c'', c''' ↦ c`, which
maps `G'` to a formula from which `LCax` follows at once. -/
def tau : List (Nat × Form) :=
  [(0, V 0), (1, V 0), (2, V 1), (3, V 1), (4, V 2), (5, V 2), (6, V 2), (7, V 2)]

/-- `x_u ↦ τ(G'_u)`; this maps every defining premise to some `γ → γ`. -/
def sigma : List (Nat × Form) :=
  tau ++ TG.defs.map (fun (n, f) => (n, subst (sigmaOf tau) f))

def idTm (A : Form) : Tm := .lam 400 A (.hyp 400)

/-- A proof of `LCax` in `IL ⊕ S(G')`. -/
def proofLC : Tm :=
  let inst := TG.defs.foldl (fun t (_, f) => .app t (idTm (subst (sigmaOf tau) f)))
    (.ax 0 sigma)
  .lam 401 ((V 0 ⟶ V 1) ⟶ V 2) <| .lam 402 ((V 1 ⟶ V 0) ⟶ V 2) <|
    .app (.app (.app (.app (.app (.app (.app inst (idTm (V 0))) (idTm (V 1)))
      (idTm (V 2))) (idTm (V 2))) (.hyp 401)) (.hyp 402))
      (.lam 403 ((V 0 ⟶ V 1) ⟶ V 2) (.lam 404 ((V 1 ⟶ V 0) ⟶ V 2) (idTm (V 2))))

/-! ## Minimality of `S(G')` in `CL` -/

/-- `Repl D z t t'`: `t'` is obtained from `t` by replacing some (possibly
no) occurrences of `D` by the variable `z`. -/
inductive Repl (D : Form) (z : Nat) : Form → Form → Prop
  | refl (t : Form) : Repl D z t t
  | here : Repl D z D (var z)
  | imp {a b a' b' : Form} : Repl D z a a' → Repl D z b b' → Repl D z (a ⟶ b) (a' ⟶ b')

def upd (σ : Nat → Form) (y : Nat) (f : Form) (p : Nat) : Form :=
  if p = y then f else σ p

theorem repl_of_subst (σ : Nat → Form) (y z : Nat) :
    ∀ β : Form, Repl (σ y) z (subst σ β) (subst (upd σ y (var z)) β)
  | var p => by
      by_cases h : p = y
      · subst h; simp only [subst, upd, ite_true]; exact .here
      · simp only [subst, upd, h, ite_false]; exact .refl _
  | imp a b => .imp (repl_of_subst σ y z a) (repl_of_subst σ y z b)

def subfs : Form → List Form
  | var p => [var p]
  | imp a b => imp a b :: (subfs a ++ subfs b)

theorem self_mem_subfs : ∀ t : Form, t ∈ subfs t
  | var _ => List.mem_singleton_self _
  | imp _ _ => List.mem_cons_self ..

theorem repl_subfs {D : Form} {z : Nat} {t t' : Form} (h : Repl D z t t')
    (hz' : Occ z t') (hz : ¬ Occ z t) : D ∈ subfs t := by
  induction h with
  | refl => exact absurd hz' hz
  | here => exact self_mem_subfs D
  | imp _ _ iha ihb =>
      simp only [Occ, not_or] at hz hz'
      refine List.mem_cons_of_mem _ (List.mem_append.2 ?_)
      rcases hz' with h | h
      · exact Or.inl (iha h hz.1)
      · exact Or.inr (ihb h hz.2)

/-- All results of replacing occurrences of `D` by `z` in a formula. -/
def repls (D : Form) (z : Nat) : Form → List Form
  | var p => if Form.beq (var p) D then [var z, var p] else [var p]
  | imp a b =>
      let r := (repls D z a).flatMap (fun a' => (repls D z b).map (fun b' => a' ⟶ b'))
      if Form.beq (imp a b) D then var z :: r else r

theorem mem_repls_imp {D : Form} {z : Nat} {a b a' b' : Form}
    (ha : a' ∈ repls D z a) (hb : b' ∈ repls D z b) : (a' ⟶ b') ∈ repls D z (a ⟶ b) := by
  have : (a' ⟶ b') ∈
      (repls D z a).flatMap (fun a' => (repls D z b).map (fun b' => a' ⟶ b')) :=
    List.mem_flatMap.2 ⟨a', ha, List.mem_map.2 ⟨b', hb, rfl⟩⟩
  simp only [repls]
  split
  · exact List.mem_cons_of_mem _ this
  · exact this

theorem self_mem_repls (D : Form) (z : Nat) : ∀ t : Form, t ∈ repls D z t
  | var p => by
      simp only [repls]; split
      · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      · exact List.mem_singleton_self _
  | imp a b => mem_repls_imp (self_mem_repls D z a) (self_mem_repls D z b)

theorem repl_mem {D : Form} {z : Nat} {t t' : Form} (h : Repl D z t t') :
    t' ∈ repls D z t := by
  induction h with
  | refl t => exact self_mem_repls D z t
  | here =>
      cases D with
      | var p => simp [repls, Form.beq_refl]
      | imp a b => simp [repls, Form.beq_refl]
  | imp _ _ iha ihb => exact mem_repls_imp iha ihb

/-- The fresh variable used for generalizations. -/
def z : Nat := 30

/-- A replacement needs to be refuted if `z` occurs in it and either the
replaced formula is compound or it is a variable that still occurs. -/
def needs (D t' : Form) : Bool :=
  occB z t' && (match D with
    | imp _ _ => true
    | var p => occB p t')

def cands : List Form :=
  (subfs SG).flatMap (fun D => (repls D z SG).filter (needs D))

def maskVal (m : Nat) (p : Nat) : Bool := Nat.testBit m p

/-- Countermodels for `cands`, in the same order; `m` makes exactly the
variables `p` with bit `p` of `m` set true. -/
def masks : List Nat := [
  0, 1253223009, 179481185, 1253222497, 1253223009, 395749949, 179481185, 179481185,
  1253223008, 1253223008, 1469491772, 1253223009, 1469491773, 1435937341, 362195519, 395749951,
  179481187, 0, 1253223015, 179481191, 1253220967, 1253223015, 179481191, 395749940,
  179481191, 1253223011, 1469491760, 1253223011, 1469491764, 1253223015, 1253223015, 179481199,
  179481199, 395749948, 0, 1872144924, 798403100, 1872136732, 1872144924, 1251387948,
  179743359, 798403100, 1872144908, 1253485167, 177646140, 1840425539, 1035119203, 1872144924,
  798403132, 2108860995, 766683747, 0, 1840425539, 766683715, 1840392771, 1840425539,
  1437772323, 364030531, 766683715, 1840425475, 1437772291, 364030563, 1840425539, 1035119203,
  1872144924, 798403132, 2108860995, 766683747, 0, 1251125772, 177383948, 395749949,
  179481185, 179481185, 1253223008, 1253223008, 1469491772, 1469491764, 1253223015, 1253223015,
  179481199, 179481199, 395749948, 1253223023, 179743343, 1, 1253485167, 179743343,
  1253354095, 1253485167, 1253223023, 179743343, 1251387948, 179743359, 798403100, 1872144908,
  1253485167, 177646140, 1, 1435675139, 361933315, 179481191, 395749940, 179481191,
  1253223011, 1469491760, 1253223011, 1253223009, 1469491773, 1435937341, 362195519, 395749951,
  179481187, 1435675139, 364030467, 5, 1437772291, 364030467, 1436723715, 1437772291,
  1435675139, 364030467, 1437772323, 364030531, 766683715, 1840425475, 1437772291, 364030563,
  5, 1253223011, 179481187, 1219668579, 1253223011, 1253223009, 1469491773, 1435937341,
  362195519, 395749951, 179481187, 179481191, 395749940, 179481191, 1253223011, 1469491760,
  1253223011, 5, 1219668579, 145926755, 179481187, 1219668579, 1251387948, 179743359,
  798403100, 1872144908, 1253485167, 177646140, 1219668579, 162703971, 33554437, 1469491772,
  395749948, 1201056316, 1469491772, 1469491764, 1253223015, 1253223015, 179481199, 179481199,
  395749948, 395749949, 179481185, 179481185, 1253223008, 1253223008, 1469491772, 33554437,
  1169336931, 95595107, 395749948, 1201056316, 1437772323, 364030531, 766683715, 1840425475,
  1437772291, 364030563, 1169336931, 229812835, 301989893, 1840425571, 766683747, 1303554659,
  1840425571, 1840425539, 1035119203, 1872144924, 798403132, 2108860995, 766683747, 1840425571,
  766683875, 301989893, 1303554659, 229812835, 1236445795, 1303554659, 1169336931, 229812835,
  766683747, 1303554659, 301989893, 1236445795, 162703971, 1228057187, 1236445795, 1219668579,
  162703971, 229812835, 1236445795, 301989893, 1228057187, 154315363, 162703971, 1228057187,
  1840425571, 766683875, 1228057187, 158509667, 310378501, 1365420547, 291678723, 364030467,
  1436723715, 1228057187, 158509667, 1365420547, 292203011, 311427077, 1365813763, 292071939,
  179743343, 1253354095, 1365420547, 292203011, 1365813763, 292137475, 311558149, 1365846531,
  292104707, 766683715, 1840392771, 1365813763, 292137475, 1365846531, 292121091, 311771140,
  1365854723, 292112899, 798403100, 1872136732, 1365846531, 292121091, 1840400963, 766663235,
  311599109, 1840403011, 766661187, 179481191, 1253220967, 1840400963, 766663235, 1365856771,
  292115971, 311600133, 1363760133, 290018309, 179481185, 1253222497, 1365856771, 292115971,
  1380537349, 306795781, 1380537349, 306795781]

def checkAll : List Form → List Nat → Bool
  | [], [] => true
  | f :: fs, m :: ms => !eval (maskVal m) f && checkAll fs ms
  | _, _ => false

theorem checkAll_sound : ∀ {fs : List Form} {ms : List Nat}, checkAll fs ms = true →
    ∀ f ∈ fs, ∃ m, eval (maskVal m) f = false
  | [], [], _, f, hf => by cases hf
  | f :: fs, m :: ms, h, g, hg => by
      simp only [checkAll, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨m, h.1⟩
      · exact checkAll_sound h.2 g hg
  | [], _ :: _, h, _, _ => by simp [checkAll] at h
  | _ :: _, [], h, _, _ => by simp [checkAll] at h

theorem cands_refuted : checkAll cands masks = true := by decide +kernel

theorem z_fresh : occB z SG = false := by decide

/-- Every relevant replacement in `S(G')` is classically invalid. -/
theorem refute {D t' : Form} (h : Repl D z SG t') (hz : Occ z t')
    (hD : (∀ p, D ≠ var p) ∨ ∃ p, D = var p ∧ Occ p t') : ¬ Valid t' := by
  intro hv
  have hz0 : ¬ Occ z SG := fun h' => by rw [← occB_iff, z_fresh] at h'; cases h'
  have hneeds : needs D t' = true := by
    simp only [needs, Bool.and_eq_true]
    refine ⟨occB_iff.2 hz, ?_⟩
    cases D with
    | imp a b => rfl
    | var p =>
        rcases hD with hD | ⟨q, hq, hocc⟩
        · exact absurd rfl (hD p)
        · cases hq; exact occB_iff.2 hocc
  have hmem : t' ∈ cands :=
    List.mem_flatMap.2 ⟨D, repl_subfs h hz hz0, List.mem_filter.2 ⟨repl_mem h, hneeds⟩⟩
  obtain ⟨m, hm⟩ := checkAll_sound cands_refuted t' hmem
  rw [hv] at hm; cases hm

/-- Replacing a variable `y` of `β` by `z` in a substitution `σ` with
`σ β = S(G')` yields a replacement of some occurrences of `σ y` in `S(G')`
by `z`, in which `z` occurs. -/
theorem generalize {σ : Nat → Form} {β : Form} (hσ : subst σ β = SG) {y : Nat}
    (hy : Occ y β) :
    Repl (σ y) z SG (subst (upd σ y (var z)) β) ∧ Occ z (subst (upd σ y (var z)) β) :=
  ⟨hσ ▸ repl_of_subst σ y z β, occ_subst hy (by simp [upd, Occ])⟩

/-- If `σ` maps the variables of `β` injectively to variables, then `σ` can
be undone. -/
theorem undo_renaming {σ : Nat → Form} {β : Form}
    (hA : ∀ y, Occ y β → ∃ p, σ y = var p)
    (hB : ∀ y₁ y₂, Occ y₁ β → Occ y₂ β → σ y₁ = σ y₂ → y₁ = y₂) :
    ∃ τ, subst τ (subst σ β) = β := by
  classical
  let τ : Nat → Form := fun p =>
    if h : ∃ y, Occ y β ∧ σ y = var p then var (Classical.choose h) else var p
  have hτ : ∀ y, Occ y β → subst τ (σ y) = var y := by
    intro y hy
    obtain ⟨p, hp⟩ := hA y hy
    have h : ∃ y, Occ y β ∧ σ y = var p := ⟨y, hy, hp⟩
    rw [hp]
    simp only [subst, τ]
    split
    · rename_i hc
      rw [hB _ _ (Classical.choose_spec hc).1 hy ((Classical.choose_spec hc).2.trans hp.symm)]
    · exact absurd h ‹_›
  have hgen : ∀ γ : Form, (∀ y, Occ y γ → subst τ (σ y) = var y) →
      subst τ (subst σ γ) = γ := by
    intro γ
    induction γ with
    | var y => intro h; exact h y rfl
    | imp a b iha ihb =>
        intro h
        simp only [subst]
        rw [iha (fun y hy => h y (Or.inl hy)), ihb (fun y hy => h y (Or.inr hy))]
  exact ⟨τ, hgen β hτ⟩

/-- The combinatorial part of the minimality of `S(G')`: no valid formula
is strictly more general than `S(G')`.

Suppose `β` is valid and `σ β = S(G')`.  For a variable `y` of `β`, the
valid formula `σ[y ↦ z] β` replaces some occurrences of `σ y` in `S(G')`
by `z` (`generalize`); by the finite check `refute`, this is impossible if
`σ y` is compound, or if `σ y` is a variable that still occurs.  Hence
`σ` maps the variables of `β` injectively to variables, and `β` is a
renaming of `S(G')` (`undo_renaming`). -/
theorem SG_no_strict_generalization :
    ¬ ∃ β, Valid β ∧ (∃ σ, subst σ β = SG) ∧ ¬ ∃ τ, subst τ SG = β := by
  rintro ⟨β, hv, ⟨σ, hσ⟩, hn⟩
  apply hn
  -- (A) `σ` maps every variable of `β` to a variable.
  have hA : ∀ y, Occ y β → ∃ p, σ y = var p := by
    intro y hy
    cases hs : σ y with
    | var p => exact ⟨p, rfl⟩
    | imp a b =>
        obtain ⟨h1, h2⟩ := generalize hσ hy
        exact absurd (valid_subst hv _) (refute h1 h2 (Or.inl (by rw [hs]; intro p h; cases h)))
  -- (B) It does so injectively.
  have hB : ∀ y₁ y₂, Occ y₁ β → Occ y₂ β → σ y₁ = σ y₂ → y₁ = y₂ := by
    intro y₁ y₂ h₁ h₂ he
    apply Classical.byContradiction
    intro hne
    obtain ⟨p, hp⟩ := hA y₁ h₁
    obtain ⟨r1, r2⟩ := generalize hσ h₁
    refine refute r1 r2 (Or.inr ⟨p, hp, ?_⟩) (valid_subst hv _)
    exact occ_subst h₂ (by
      have : upd σ y₁ (var z) y₂ = σ y₂ := by simp [upd, Ne.symm hne]
      rw [this, ← he, hp]; rfl)
  -- (C) Hence `σ` is a renaming, and `β` is an instance of `S(G')`.
  obtain ⟨τ, hτ⟩ := undo_renaming hA hB
  exact ⟨τ, by rw [← hσ]; exact hτ⟩

/-! ## `Thm` and `ThmD` coincide -/

theorem thm_iff {Ax : List Form} {φ : Form} : Thm Ax φ ↔ ThmD Ax φ := by
  constructor
  · intro h
    induction h with
    | k a b => exact .k a b
    | s a b c => exact .s a b c
    | ax hB σ => exact .ax hB σ
    | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  · intro h
    unfold ThmD at h
    induction h with
    | k a b => exact .k a b
    | s a b c => exact .s a b c
    | ax hB σ => exact .ax hB σ
    | hyp h => cases h
    | mp _ _ ih1 ih2 => exact .mp ih1 ih2

/-- A closed λ-term accepted by the checker yields a theorem. -/
theorem Thm.of_proves {Ax : List Form} {t : Tm} {φ : Form}
    (h : proves Ax t φ = true) : Thm Ax φ :=
  thm_iff.2 (ThmD.of_proves h)

/-- If `B ∈ IL ⊕ Ax`, then `IL ⊕ B ⊆ IL ⊕ Ax`. -/
theorem Thm.transfer1 {Ax : List Form} {B : Form} (hB : Thm Ax B) {φ : Form}
    (h : Thm [B] φ) : Thm Ax φ :=
  thm_iff.2 (ThmD.transfer (by simp only [List.mem_singleton]; rintro _ rfl; exact thm_iff.1 hB)
    (thm_iff.1 h))

/-- If `B` is classically valid, then so is every theorem of `IL ⊕ B`. -/
theorem Thm.valid1 {B φ : Form} (hB : Valid B) (h : Thm [B] φ) : Valid φ :=
  ThmD.valid (by simp only [List.mem_singleton]; rintro _ rfl; exact hB) (thm_iff.1 h)

/-! ## Ingredients of the main theorems -/

/-- `S(G') ∈ LC`, by the explicit derivation `proofSG`. -/
theorem SG_in_LC : Thm [LCax] SG := Thm.of_proves (t := proofSG) (by decide +kernel)

/-- `LCax ∈ IL ⊕ S(G')`, by the explicit derivation `proofLC`. -/
theorem LC_in_ILSG : Thm [SG] LCax := Thm.of_proves (t := proofLC) (by decide +kernel)

theorem LCax_valid : Valid LCax := by
  intro v; simp only [LCax, V, eval]; cases v 0 <;> cases v 1 <;> cases v 2 <;> rfl

theorem SG_valid : Valid SG := Thm.valid1 LCax_valid SG_in_LC

/-! ## Results

These have exactly the statements of the theorems in `Main.lean`. -/

/-- `IL ⊕ S(G') = LC`. -/
theorem IL_SG_eq_LC_proof (φ : Form) : Thm [SG] φ ↔ Thm [LCax] φ :=
  ⟨Thm.transfer1 SG_in_LC, Thm.transfer1 LC_in_ILSG⟩

/-- `S(G')` is minimal in `CL`. -/
theorem SG_minimal_proof : MinimalCL SG := ⟨SG_valid, SG_no_strict_generalization⟩

/-- `S(G')` has order `4`. -/
theorem SG_ord_proof : ord SG = 4 := by decide

end SGprimeDirect
