# Paper plot: Every Intermediate Logic is Axiomatizable by Formulas Minimal in Classical Logic

Sources:
`implicational_minimalization_proof.md` (implicational, IL),
`full_language_minimalization_proof.md` (full language, IPC),
`paper/` (order-4 paper: St preserves minimality).

## 0. Title

**Every Intermediate Logic is Axiomatizable by Formulas Minimal in Classical Logic**

Echoes the title of NM21 ("On Implicational Intermediate Logics Axiomatizable
by Formulas Minimal in Classical Logic"). The title covers both the
implicational case (Corollary D) and the full language (Theorem E); the
abstract must say that both are meant.

---

## 1. Main message

For every classical tautology Φ there is a formula M that is minimal in CL
with respect to the substitution preorder and generates the same axiomatic
extension: IL + M = IL + Φ. Moreover M can be taken of order ≤ 4 and of size
linear in Φ.

Consequences:

1. Every (implicational) intermediate logic is axiomatizable by CL-minimal
   formulas of order ≤ 4. This answers Komori--Kashima's question in the
   strongest possible negative form, and answers [NM21, Open Problem 1]
   ("which intermediate logics are so axiomatizable?"): all of them.
2. [NM21, Open Problem 2] (order 4) follows as a special case.
3. Minimality in CL imposes no restriction on axiomatizability; what matters
   is order (≤ 3 ⇒ IL in the implicational language).

Phrase it this way: being axiomatizable by minimal formulas is not a
property of a logic but a matter of the presentation of its axioms.

---

## 2. Main results (statements for the introduction)

**Definition.** A formula Φ ∈ CL is *minimalizable* over a logic L₀ if there
is M ∈ Min(CL) with L₀ + M = L₀ + Φ.

**Theorem A (implicational).** For every implicational Φ ∈ CL one can
construct, in linear time, an implicational M_Φ ∈ Min(CL) such that

- IL ⊢ Φ → M_Φ, and IL ⊢ σ(M_Φ) ↔ Φ for a substitution σ fixing Var(Φ);
- hence IL + M_Φ = IL + Φ;
- |M_Φ| = 102L − 2V − 38, |Var(M_Φ)| = 26L + V − 7, ord(M_Φ) ≤ 7.

**Theorem B (Statman, from the order-4 paper).** If α ∈ Min(CL), then
St(α) ∈ Min(CL), IL + St(α) = IL + α, and ord(St(α)) ≤ 4.

**Corollary C.** M̂_Φ := St(M_Φ) satisfies M̂_Φ ∈ Min(CL),
IL + M̂_Φ = IL + Φ, ord(M̂_Φ) ≤ 4, and |M̂_Φ| = 3|M_Φ| − 2 = O(L).

**Corollary D.** For every set Σ ⊆ CL, IL + Σ = IL + {M̂_Φ : Φ ∈ Σ}. Hence every
implicational intermediate logic is axiomatizable by CL-minimal formulas of
order ≤ 4, and 4 is optimal for every logic other than IL
(Prop. order3: CL ∩ ord ≤ 3 ⊆ IL).

**Theorem E (full language {⊥, ∧, ∨, →}).** For every Φ ∈ CPC there is a
directly constructed M_Φ ∈ Min(CPC) with IPC + M_Φ = IPC + Φ,
ord(M_Φ) ≤ 4 and |M_Φ| = 102L − 48B₊ − 8B₋ − 2V − 48. Statman is not needed.
Hence every intermediate logic (in the usual sense) is axiomatizable by
CPC-minimal formulas of order ≤ 4.

**Remark F (full language lower bounds).** The order lower bound depends on
the language: p ∨ (p → q) is a CPC-minimal axiom of CPC of order 2, and
(p → q) ∨ ((p → ⊥) → r) is a CPC-minimal axiom of KC of order 3. ⊥ cannot be
eliminated in general (KC and IPC have the same ⊥-free theorems).

**Proposition G (principal-type reading).** Assume principal types exist for
the λ-calculus with constants for L-axiom schemes (e.g. callcc : P for CL).
Then α ∈ Min(L) iff α is the principal type of every closed term of type α.
Since Min(CL) ∩ L ⊆ Min(L) for L ⊆ CL, Corollary D reads: every intermediate
logic is axiomatized by types that are principal for all their classical
inhabitants.

- Contrast with Hindley's converse principal type theorem (every inhabited
  type is the principal type of *some* term): ∃ vs. ∀ over inhabitants.
- Reading: every classical proof of M̂_Φ uses every variable identification
  and every subformula of M̂_Φ; shape rigidity costs no axiomatic power.
- Place: Remark in §1 (related work) + short subsection in §7; the proof is
  a few lines, so do not present it as a main theorem.
- Related work paragraph (cite):
  - [Hin69] converse principal type theorem (∃ version; in IL it covers all
    inhabited types, so ∃ ≠ ∀ = Min).
  - [Hir92] (abstract): BCK-minimal formulas = principal type-schemes of
    βη-normal BCK-λ-terms; [Hir93] journal treatment of principal types of
    BCK-λ-terms; [Hir91] relevantly balanced formulas have unique normal
    proofs. Uniqueness of the βη-normal inhabitant of a BCK-minimal formula
    (Hirokawa's conjecture): Wroński, Hirokawa, Tatsuta (independently;
    Wroński via the coherence theorem for CCCs, cf. Mints); published proof:
    [Tat06, Thm 4.2] (BCK β-normal proofs of minimal formulas are D-normal).
    Do not cite Wroński unless a written source is found. So in BCK: ∃-principal = ∀-principal = Min = unique
    normal inhabitant.
  - [Tat93] in NJ, β-normal proofs of minimal formulas of depth 2 are unique;
    at depth 3 βη-normal proofs need not be unique, in NJ and in NK.
    Hence beyond BCK, minimality gives principality but not uniqueness;
    M̂_Φ (order 4) should not be claimed to have unique inhabitants.
  - Note: Komori's BCK version of the KK problem concerns CL-minimal axioms
    over BCK, not BCK-minimality; its difficulty for us is contraction.
- Check before citing: theorem numbers in [Hir93], [Tat93]; Tatsuta's
  "depth" vs. our order; Wroński's paper (title/venue); principal types with
  typed constants / λμ.

References to add:
- [Hin69] J. R. Hindley, The principal type-scheme of an object in
  combinatory logic, Trans. AMS 146 (1969) 29--60.
- [Hir92] S. Hirokawa, Balanced formulas, BCK-minimal formulas and their
  proofs, LFCS '92, LNCS 620 (1992). doi:10.1007/BFb0023874 (check pages)
- [Hir93] S. Hirokawa, Principal types of BCK-lambda-terms, Theoret. Comput.
  Sci. 107(2) (1993) 253--276.
- [Tat93] M. Tatsuta, Uniqueness of normal proofs of minimal formulas,
  J. Symbolic Logic 58(3) (1993) 789--799.
- [Wro??] A. Wroński: no written source found (2026-10-22). Only secondary
  mention: M. Kanazawa, TRENDS XIII talk slides. Hirokawa cites an
  unpublished Wroński manuscript "On Bunder and Meyer's theorem" (1987);
  possibly unrelated. Ask Komori / Kanazawa, or check MathSciNet.
- [Hir91] S. Hirokawa, BCK-formulas having unique proofs, CTCS '91,
  LNCS 530 (1991) 106--120. doi:10.1007/BFb0013460.
- [Tat06] M. Tatsuta, NII Technical Report NII-2006-011E (title: check);
  Sect. 4, Prop. 4.1, Thm 4.2 (BCK case).
- [AO94] T. Aoto and H. Ono, Non-uniqueness of normal proofs for minimal
  formulas in implication-conjunction fragment of BCK, Bull. Sect. Logic
  23(3) (1994) 104--112.
- [Aot99] T. Aoto, Uniqueness of normal proofs in implicational
  intuitionistic logic, J. Logic Lang. Inform. 8(2) (1999) 217--242.
- [KH93] Y. Komori and S. Hirokawa, The number of proofs for a BCK-formula,
  J. Symbolic Logic 58(2) (1993) 626--628. doi:10.2307/2275222.
  (Necessary and sufficient condition for a BCK-formula to have a unique
  normal form proof.)

---

## 3. Section structure (target 20–25 pp.)

### §1 Introduction (3 pp.)

Narrative: the expected answer was "minimality is very restrictive";
the actual answer is the opposite extreme. References are to NM21
(Studia Logica 109 (2021) 1413--1422) unless stated otherwise.

1. **Setting.** Komori's substitution preorder ≤_sub [Kom87]; minimal formulas;
   K, S, P are minimal in CL [NM21, Ex. 2.3], so IL and CL are axiomatizable
   by CL-minimal formulas. Most familiar axioms are not minimal
   (e.g. Dummett's G [NM21, Ex. 2.4]).
2. **The expectation.** Komori and Kashima (2005) asked whether IL and CL are
   the only implicational intermediate logics axiomatizable by CL-minimal
   formulas; Komori's original conjecture is stronger: over BCK only
   BCK, IL, CL [Kom05, Kom07 Conj. 4.1; NM21 fn. 1]. Evidence for a positive
   answer: Kashima's partial positive solution via a sequent calculus
   [Kas05], his note "On non-generality of axioms of intermediate
   propositional logics" [Kas05b], and the computer search in
   [NM21, Remark 3.4], which found no small counterexample.
3. **The first counterexample.** NM21 found G' with IL + G' = LC by an
   *ad hoc* construction [NM21, Sect. 4], verified by checking 22 predecessors
   in Coq. They asked how many intermediate logics are so axiomatizable and
   whether the class can be characterized [Open Problem 1], and whether
   order 4 suffices [Open Problem 2]. In the full language, only KC was known
   (Kashima's J, Hirai's J', J'') [NM21, Remark 1.1].
4. **This paper (surprise).** Every implicational intermediate logic is
   axiomatizable by CL-minimal formulas; in fact each single axiom Φ can be
   replaced by a CL-minimal M with IL + M = IL + Φ, of order ≤ 4, constructed
   uniformly in linear time (Theorem A, Corollaries C, D). The same holds for
   all intermediate logics in {⊥, ∧, ∨, →} (Theorem E). Thus:
   - Komori--Kashima: negative in the strongest form (no proper
     intermediate logic is excluded);
   - Open Problem 1: the class is the class of *all* implicational
     intermediate logics;
   - Open Problem 2: yes, and order 4 is optimal (Prop. order3);
   - full language: Remark 1.1 extended from KC to every logic.
   Formulation to use: axiomatizability by minimal formulas is not a property
   of the logic but of the presentation of its axioms.
5. **Comparison with NM21 Prop. 3.3.** NM21 showed that every implicational
   intermediate logic is axiomatizable by *simple* formulas (removing the
   abstractions [q → r/p]). Simplicity only excludes the abstraction of
   implications between fresh distinct variables; minimality also requires
   excluding every variable split and every abstraction of repeated
   subformulas. Our construction does this by local constraints
   (selectors + query copies) and spanning trees of ports.
6. **Method in one paragraph.** Two layers: localization (Theorem A; order ≤ 7)
   and order reduction by the minimality-preserving Statman translation
   (Theorem B). In the full language ∧ removes the need for the second layer.
7. **What remains.** Komori's BCK version (our construction uses contraction),
   Open Problem 3 (independent axiom systems) — not addressed.

Related work (end of §1): extension variables (Tseitin, Statman,
Plaisted--Greenbaum, Mints), Jeřábek's φ⁺; check whether anything similar
appears in work on projective formulas / unification.

### §2 Preliminaries (2 pp.)
- Language, IL, CL, L + Γ, order, polarity, size.
- Substitution preorder; mutual instances = renaming.
- **Criterion (Lemma 2.1).** α ∈ Min(CL) iff no nontrivial atom split
  and no abstraction of a nonempty selection of copies of one compound
  subformula is in CL. Full language: add ⊥ abstraction.
  Source: Matsuda (2015) Lemma 4.4; the order-4 paper Prop. cor:criterion.
  Give a proof (short) since the selection-of-copies version is needed.

### §3 Local constraints (2 pp.) — common to both languages
- Node variables t_v, polarity-dependent constraints C_v (table).
- Lemma: 𝒞 ⊢ Φ_v → t_v (pos), t_v → Φ_v (neg).
- Lemma: t_v := Φ_v makes every C_v an instance of reflexivity;
  standard valuation ν.
- Lemma: each leaf of C_v is sensitive (read-once formula).

### §4 Stage 1: selectors and query copies (3 pp.)
- H_i = x_i → C_i, K_i = s → x_i, Q₀ = s → r.
- Implicational: F_Φ = Γ → (Q₀ → Γ^copy → D) → D.
- Lemma: IL + F_Φ = IL + Φ (via ρ).
- Lemma: every variable occurs in both polarities.
- **Lemma: every single-occurrence split of F_Φ is refuted** (case table;
  the selectors let one constraint be refuted in isolation).
  Note: this lemma does not use Φ ∈ CL except for the Q₀/r rows.

### §5 Stage 2: ports, guards, spanning trees (3 pp.)
- Ports u_o, guards a → u_o / u_o → a, edges n → p (spanning tree on P_a ∪ N_a).
- M_Φ = G → (F° → R → d) → d.
- Lemma: IL + M_Φ = IL + F_Φ (via τ); Corollary: σ = ρ∘τ.

### §6 Minimality of M_Φ (3 pp.)
- Atom splits: center (tree connectivity), port (edge-side / body-side,
  reduces to §4), terminal d.
- Abstraction: necessary condition (an atomic pair a → b containing all
  occurrences of a and b), and M_Φ has no such pair.
- **Theorem A.** Size and order count.

### §7 Order reduction by the Statman translation (3–4 pp.)
Two options (see §5 of this plot):
- (i) self-contained: definition of St, ord ≤ 4, soundness over IL,
  minimality preservation proof (shape lemma, key lemma);
- (ii) cite the order-4 paper and state Theorem B only.
- Corollaries C, D; optimality of order 4 (Prop. order3).
- Example: Peirce (366 leaves after Theorem A; 1096 after St), and
  comparison with St(G') (67 leaves) to show the general construction is
  not size-optimal.

### §8 The full language (4 pp.)
- Criterion with ⊥ abstraction; positive ⊥ is never minimal.
- Constraint table for ∧, ∨, ⊥; standard valuation needed instead of all-1.
- Stage 1 with ∧: F_Φ = ⋀Γ → (Q₀ ∧ ⋀Γ̂), asymmetric copy x_i → t_v → b_i.
- Stage 2: M_Φ = ⋀G → (F° ∧ ⋀R); ord ≤ 4 directly.
- Theorem E. Remark F (order 2, 3 examples; ⊥ not eliminable).
- Alternative check: St for FLew full language from the order-4 paper also
  applies; mention but not needed.

### §9 Concluding remarks and open problems (1 pp.)
- Base logics other than IL: BCK (Komori's original setting), BCI.
  Stage 1 uses Γ twice (contraction) and Stage 2 duplicates ports, so the
  construction is IL-specific. Is every BCK-extension axiomatizable by
  CL-minimal formulas?
- Size: least size / number of variables of a minimal representative.
- Full language: least order of a CPC-minimal axiom for each logic
  (e.g. is KC axiomatizable by an order-2 minimal formula?).
- Minimality in logics other than CL (e.g. Min(L) for L ≠ CL).
- Independence of axiom sets preserved?

### Appendix
- Proof of the criterion (if not in §2).
- Computational verification (`implicational_minimality_localization.py`):
  ranges in note §11 (9,341 inputs etc.); state as a check, not a proof.
- (optional) Lean formalization of Theorem B.

---

## 4. Points to verify before writing

1. Literature: is "every intermediate logic has a CL-minimal axiomatization"
   already known? Read Kashima [Kas05b] (NM21 ref. [7], "On non-generality of
   axioms of intermediate propositional logics") and Kashima's partial
   positive solution [Kas05] carefully: the "partial positive solution" must
   be consistent with our result (state precisely which class it covers).
   Also Komori 2007 (MSJ, "Propositional logics revisited").
   If we claim "continuum many", check the cardinality of the lattice of
   implicational intermediate logics (otherwise do not claim it).
2. Criterion with *selections* of copies: confirm Matsuda 2015 Lemma 4.4
   states it in this form; otherwise our proof is the reference.
3. Implicational order: ord(F_Φ) ≤ 5, ord(M_Φ) ≤ 7 (check (8.5) once more;
   only the final ≤ 4 is used in theorems).
4. Full language order convention: ord(A ∧ B) = ord(A ∨ B) = max; ord(⊥) = 1?
   Fix and use consistently in Remark F.
5. Size of St: |St(α)| = 3|α| − 2; check against translation.tex.
6. Theorem E: the case Φ with B₋ = 0 and the case where a ⊥-node is the root
   of a subformula used only positively — re-run the script on ⊥-inputs.

---

## 5. Relation to the order-4 paper (decision needed)

The new result makes the order-4 paper's Corollary LC a special case
(St(M_Dummett) is another order-4 minimal axiom of LC, though much larger
than St(G')).

- **Option 1 (recommended): merge.** One paper; Theorem B with proof in §7;
  keep the BCI soundness, ord-3 proposition, St(G') as an explicit small
  example. Move the substructural extensions and necessity-of-I results
  to a separate short paper or drop them.
- **Option 2: two papers.** Paper I: "Statman translation preserves
  minimality" (substructural, Lean, St(G')). Paper II: this paper, cites
  Paper I for Theorem B. Risk: Paper II depends on an unpublished result;
  submit Paper I first or simultaneously.

---

## 6. Draft abstract

A formula is minimal in a logic L if it belongs to L and no strictly more
general formula with respect to the substitution preorder belongs to L.
Komori and Kashima asked whether intuitionistic and classical logic are the
only implicational intermediate logics axiomatizable by formulas minimal in
classical logic CL. Nakamura and Matsuda refuted this with an ad hoc axiom
of Gödel--Dummett logic and asked which logics are so axiomatizable.
Surprisingly, all of them are: for every
implicational classical tautology Φ we construct, in linear time, a formula
M_Φ minimal in CL such that IL + M_Φ = IL + Φ. Combined with a
minimality-preserving Statman translation, M_Φ can be taken of order at most
4, which is optimal. The same holds in the language {⊥, ∧, ∨, →} with order at
most 4 obtained directly. Consequently, every intermediate logic is
axiomatizable by formulas of order at most 4 minimal in classical logic.

---

## 7. Venue

**Decision (2026-10-22): target JSL**, fallback Studia Logica. Lead with
(i) minimality is a property of presentations, not of logics, and
(ii) the principal-type reading (∀ inhabitants vs. Hindley's ∃).
Draft: `paper_jsl/`.

- **Studia Logica**: natural choice (NM21 appeared there; Komori--Kashima
  problem is known to its readers).
- **Journal of Symbolic Logic**: possible, since the paper completely answers
  the Komori--Kashima problem (NM21 Open Problems 1 and 2). Higher bar; the
  introduction must argue the general interest (axiomatization vs.
  presentation).
- **Archive for Mathematical Logic**, **Notre Dame Journal of Formal Logic**,
  **Mathematical Logic Quarterly**: suitable for a 20–25 page technical paper.
- **Journal of Logic and Computation**, **Logic Journal of the IGPL**: if the
  linear-time construction / verification aspect is emphasized.
- Short version: WoLLIC (LNCS) or Bulletin of the Section of Logic.
