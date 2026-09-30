# Paper plan: A Minimality-Preserving Statman Translation

## Working title

**A Minimality-Preserving Statman Translation for Implicational Logic**

Alternative titles:

- **Statman Translation Preserves Substitution Minimality**
- **Reducing Minimal Implicational Axioms to Order Four**
- **Minimal Implicational Axioms of Order Four via Statman Translation**

The first title is probably the cleanest if the translation theorem is the main point.

---

## 1. Main message

Let \(A\) be a purely implicational formula and let \(S(A)\) be the polarity-aware
Statman / extension-variable translation.

The paper should not be presented primarily as the construction of one more
counterexample to the Komori--Kashima problem.

The conceptual statement is:

> **Statman translation preserves minimality with respect to the substitution
> preorder.**

Together with the standard correctness of the translation and the elementary
order bound, this gives:

\[
A\text{ is CL-minimal}
\quad\Longrightarrow\quad
\begin{cases}
S(A)\text{ is CL-minimal},\\
IL+A=IL+S(A),\\
\operatorname{Ord}(S(A))\le 4.
\end{cases}
\]

Thus every intermediate logic that has a CL-minimal implicational axiom also
has such an axiom of order at most \(4\).

In particular, applying this to the Nakamura--Matsuda axiom for \(LC\) resolves
their order-\(4\) open problem negatively.

---

## 2. Suggested main theorem

### Theorem 1 (Minimality-preserving Statman translation)

For every implicational formula \(A\), one can construct in linear time an
implicational formula \(S(A)\) such that:

1. \(IL+A=IL+S(A)\);
2. \(\operatorname{Ord}(S(A))\le 4\);
3. if \(A\) is minimal in \(CL\) with respect to the substitution preorder,
   then \(S(A)\) is minimal in \(CL\).

The size bound can also be stated explicitly:

\[
|S(A)|=O(|A|).
\]

If desired, separate this into three lemmas and state the combined theorem at
the end.

---

## 3. Strong corollary

### Corollary 2

If an implicational intermediate logic \(L\) is of the form

\[
L=IL+A
\]

for some \(CL\)-minimal implicational formula \(A\), then there exists a
\(CL\)-minimal implicational formula \(B\) of order at most \(4\) such that

\[
L=IL+B.
\]

More generally, if \(L\) is axiomatizable over \(IL\) by a set
\(\Gamma\) of \(CL\)-minimal implicational formulas, then

\[
L=IL+\{S(A):A\in\Gamma\},
\]

and every \(S(A)\) is \(CL\)-minimal and has order at most \(4\).

Hence restricting minimal axioms to order at most \(4\) does not reduce the
class of intermediate logics obtainable from \(CL\)-minimal implicational
axioms.

This is arguably the cleanest conceptual consequence.

---

## 4. Application to the Komori--Kashima problem

Nakamura--Matsuda constructed a \(CL\)-minimal implicational formula \(G'\)
such that

\[
IL+G'=LC.
\]

Their construction has order \(5\), and they left open whether there exists a
proper intermediate logic axiomatizable by \(CL\)-minimal formulas of order at
most \(4\).

Apply Theorem 1 to \(G'\). Then

\[
IL+S(G')=LC,
\]

\(S(G')\) is \(CL\)-minimal, and

\[
\operatorname{Ord}(S(G'))\le4.
\]

Therefore:

### Corollary 3

There exists a proper implicational intermediate logic axiomatizable by a
formula minimal in \(CL\) and of order at most \(4\).

In fact \(LC\) is such a logic.

Thus Nakamura--Matsuda's Open Problem 2 has a negative answer.

The explicit formula \(S(G')\) need not be printed in full in the main text.
It can be given in an appendix or generated mechanically.

---

## 5. Definition of the translation

For each implication occurrence \(u\) of \(A\), introduce a fresh variable
\(x_u\).

For an occurrence \(u\), define its representative \(r_u\) by

\[
r_u =
\begin{cases}
p,&u\text{ is an occurrence of the atom }p,\\
x_u,&u\text{ is an implication occurrence}.
\end{cases}
\]

Give the root positive polarity. For

\[
u=(v\to w),
\]

the antecedent occurrence \(v\) receives the opposite polarity and the
consequent occurrence \(w\) receives the same polarity.

Define the link associated with \(u\) by

\[
E_u=
\begin{cases}
(r_v\to r_w)\to x_u,&u\text{ positive},\\
x_u\to(r_v\to r_w),&u\text{ negative}.
\end{cases}
\]

If \(u_1,\ldots,u_m\) are the implication occurrences, define

\[
S(A)=E_{u_1}\to\cdots\to E_{u_m}\to r_{\mathrm{root}}.
\]

The order bound is immediate:

\[
\operatorname{Ord}(E_u)\le3,
\]

and therefore

\[
\operatorname{Ord}(S(A))\le4.
\]

---

## 6. Correctness / equivalence of axioms

This section should be short.

### Lemma 4

\[
IL\vdash A\to S(A).
\]

Proof: under all links \(E_u\), prove by induction on occurrences that

\[
u\text{ positive}\Rightarrow A_u\to r_u,
\]

and

\[
u\text{ negative}\Rightarrow r_u\to A_u.
\]

Apply this at the positive root.

### Lemma 5

\[
A\in IL+S(A).
\]

Substitute

\[
x_u:=A_u
\]

for every extension variable. Every link becomes an instance of

\[
B\to B.
\]

The conclusion becomes \(A\). Since a logic is closed under substitution and
modus ponens, \(A\in IL+S(A)\).

Hence

\[
IL+A=IL+S(A).
\]

This is the standard extension-variable / Statman correctness argument and
should not occupy much space.

---

## 7. Minimality theorem

This should be the technical core of the paper.

### Step 1. Minimal formulas are simple

Use the definition of simplicity from Nakamura--Matsuda.

If

\[
A=[q\to r/p]B
\]

with fresh distinct \(q,r\), then

\[
A\in CL\Longrightarrow B\in CL,
\]

because over Boolean valuations the value of \(q\to r\) can independently be
chosen to be either \(0\) or \(1\).

Consequently every \(CL\)-minimal formula is simple.

### Step 2. Simplicity is preserved

Show

\[
A\text{ simple}\Longrightarrow S(A)\text{ simple}.
\]

An extension variable \(x_u\) cannot participate in a destructible pair
\(q\to r\), since one of its two occurrences occurs at the outer level of its
own defining link

\[
(r_v\to r_w)\to x_u
\]

or

\[
x_u\to(r_v\to r_w),
\]

where the other side is non-atomic.

Thus any destructible pair in \(S(A)\) must consist of original variables.
Such a pair corresponds directly to a destructible pair in \(A\).

### Step 3. Use Nakamura--Matsuda Proposition 3.2

Since \(S(A)\) is simple, it suffices to consider immediate predecessors
obtained by splitting occurrences of one variable into two nonempty classes.

There are two cases.

---

## 8. Split of an original variable

Suppose an original variable \(p\) is split into \(p,p'\).

Perform exactly the same occurrence split in \(A\), obtaining \(B\). Then

\[
B<_\mathrm{sub}A.
\]

The corresponding predecessor of \(S(A)\) is, up to renaming extension
variables,

\[
S(B).
\]

If it were classically valid, then by correctness of the translation \(B\)
would be classically valid.

This contradicts minimality of \(A\).

---

## 9. Split of an extension variable

Let \(x_u\) be the extension variable corresponding to a complex occurrence
\(u\).

It occurs exactly twice:

1. in its defining link;
2. in the parent link, or as the final root representative.

Split those two occurrences.

Let \(z\) be a fresh variable and let

\[
B:=A[u:=z],
\]

where the whole occurrence \(A_u\) is replaced by \(z\).

Then

\[
B<_\mathrm{sub}A,
\]

since substituting \(A_u\) for \(z\) recovers \(A\).

The key lemma is:

### Splitting Lemma

If the split predecessor of \(S(A)\) associated with \(x_u\) is classically
valid, then \(B\) is classically valid.

Proof by contraposition.

Given a Boolean countervaluation for \(B\), extend it to the extension
variables as follows:

- below \(u\): give every extension variable the truth value of its
  represented subformula of \(A_u\);
- on the defining-link copy of \(x_u\): use the truth value of \(A_u\);
- on the parent-side copy of \(x_u\): use the truth value assigned to \(z\);
- elsewhere: use the truth values of the corresponding subformulas of \(B\).

Then every link is true, while the root representative has the same truth
value as \(B\), hence is false.

Thus the split predecessor is not classically valid.

Therefore validity of the predecessor would imply \(B\in CL\), contradicting

\[
B<_\mathrm{sub}A
\]

and minimality of \(A\).

This proves the minimality-preservation theorem.

---

## 10. Recommended paper structure

A short paper could be around 6--10 pages.

### 1. Introduction
About 1 page.

- substitution-minimal formulas;
- Komori--Kashima problem;
- Nakamura--Matsuda counterexample;
- their remaining order-\(4\) question;
- contribution: Statman translation preserves minimality;
- order-\(4\) result becomes an immediate corollary.

### 2. Preliminaries
About 1 page.

- implicational formulas;
- substitution preorder;
- \(CL\)-minimality;
- order;
- simple formulas;
- quote Nakamura--Matsuda Proposition 3.2.

### 3. Statman translation
About 1--2 pages.

- definition;
- linear size;
- order at most \(4\);
- \(IL+A=IL+S(A)\).

### 4. Preservation of minimality
About 2--3 pages.

- minimal implies simple;
- \(S\) preserves simplicity;
- original-variable split;
- extension-variable split;
- main theorem.

### 5. Consequences
About 1 page.

- universal order-\(4\) reduction;
- application to \(LC\);
- negative solution of the order-\(4\) open problem.

An appendix can contain the explicit \(S(G')\) and Lean verification.

---

## 11. What should *not* be the main proof

Avoid making the paper's core argument:

> We generated \(S(G')\), enumerated its 44 predecessors, and checked all of
> them by SAT/Lean.

That is useful as verification, but it obscures the conceptual result.

The 44-case computation should instead be presented as an independent
machine check of the concrete application.

The main mathematical argument should be the general preservation theorem.

---

## 12. Suggested abstract

We study formulas minimal in classical implicational logic with respect to the
substitution preorder. We show that a polarity-sensitive Statman
extension-variable translation preserves this minimality. More precisely, for
every implicational formula \(A\) we construct in linear time an implicational
formula \(S(A)\) of order at most four such that \(IL+A=IL+S(A)\), and prove
that \(S(A)\) is minimal in \(CL\) whenever \(A\) is. Consequently, every
intermediate logic axiomatizable over \(IL\) by a \(CL\)-minimal implicational
formula admits such an axiom of order at most four. Applying the construction
to the counterexample of Nakamura and Matsuda yields an order-four
\(CL\)-minimal axiom for Gödel--Dummett logic, answering negatively their
remaining question concerning formulas of order at most four.

---

## 13. Novelty / literature check

The standard literature around Statman's translation discusses polynomial
translation, extension variables, and preservation of intuitionistic
provability.

Nakamura--Matsuda study substitution-minimal implicational formulas and give
the criterion for checking minimality of simple formulas.

A preliminary literature search did not reveal a statement that Statman's
extension-variable translation preserves minimality in the substitution
preorder.

Before submission, however, a more systematic search should be made around:

- Statman's original translation;
- extension variables in intuitionistic proof complexity;
- substitution-minimal formulas;
- projective formulas / most general unifiers, in case an equivalent
  preservation observation is known under different terminology.

The novelty claim should initially be phrased conservatively as a
minimality-preservation property of this particular polarity-aware
implicational Statman translation.

---

## 14. References to start from

- R. Statman, *Intuitionistic Propositional Logic is Polynomial-Space
  Complete*, Theoretical Computer Science 9 (1979), 67--72.
- Y. Nakamura and N. Matsuda, *On Implicational Intermediate Logics
  Axiomatizable by Formulas Minimal in Classical Logic: A Counter-Example to
  the Komori--Kashima Problem*, Studia Logica 109 (2021), 1413--1422.
- A. Hertel and A. Urquhart, work on proof complexity of intuitionistic
  propositional logic and extension-variable presentations of Statman's
  translation.
