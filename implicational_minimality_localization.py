#!/usr/bin/env python3
"""
UNIVERSAL IMPLICATIONAL MINIMALIZATION BY SELECTOR MONITORING
============================================================

Standalone Python 3.10+; standard library only. Run without -O or -OO:

    python implicational_minimality_localization.py

The mathematical result, its limitation, and the finite audit are different
claims. The proof below applies to arbitrary finite pure implicational CL
tautologies. The executable audit independently exhausts the stated finite
range; it is not a substitute for that proof. The two linear constructions
below transform EVERY pure implicational CL tautology into a substitution-
minimal CL tautology generating the same pure IL axiom theory. No Statman
translation is implemented here. The result has raw order at most 7; applying
a separately established minimality- and axiom-theory-preserving order-4 translation is a
separate final step.

CONVENTIONS
-----------
A formula is a nonempty atom name (str), or a pair (antecedent, consequent).
All displayed implication chains associate to the right. IL means the pure
implicational fragment of intuitionistic logic, with uniform substitution as
part of the axiom schema convention. CL means classical propositional logic.
The order convention is ord(atom)=1 and ord(A->B)=max(ord(A)+1,ord(B)).

An atomic defect is a nontrivial partition of the occurrences of one atom
into two names that leaves a CL tautology. Complementary partitions are
identified, since they differ only by renaming the two atom names. A singleton
defect isolates one occurrence of a REPEATED atom. A variable that occurs
only once has no proper split: renaming that occurrence is not a defect.

Full substitution minimality additionally prohibits replacing any nonempty
selection of occurrences of one equal compound subtree by a fresh atom,
while retaining CL validity. Atom splits and these compound abstractions
form a complete elementary test: any proper substitution generalization can
be reached by a sequence of such elementary generalizations. If its endpoint
is CL valid, its intermediate instances are CL valid too.

THE CONSTRUCTION
----------------
Let Phi be a CL tautology. Write L for its leaf count, V for its number of
variables, s for the number of variables occurring exactly once, and h for
the number of repeated variables that occur in only one polarity. Polarity
is positive at the root and reverses on entering an antecedent.

Replace EACH occurrence of a repeated atom x by its own fresh port. Leave
globally singleton variables unchanged. The resulting BODY has distinct
atom names at all of its leaves. For a positive port p add the guard x->p;
for a negative port n add n->x. If x originally has only one polarity, add
one fresh dummy port of the opposite polarity and its guard. Dummy ports
do not occur in BODY. Let Gamma be the resulting list of guards.

For each repeated x, choose positive and negative anchors p0,n0. Add the
following queries, a spanning tree on the complete bipartite port graph:

    n -> p0       for every negative port n;
    n0 -> p       for every positive port p other than p0.

Let R1,...,RE be all these queries and D an additional fresh atom. Define

    F(Phi) = Gamma -> (BODY -> R1 -> ... -> RE -> D) -> D.

All generated names are chosen outside the input's atom set. The constructor
works syntactically for arbitrary formulas; the conclusions below assume
that Phi is CL valid. No Boolean enumeration is needed for construction.

There are L-s+h guards and E=L-V+h queries. Consequently

    leaves(F)    = 5L - 2V - 2s + 4h + 2;
    variables(F) = L + V - s + h + 1;
    ord(F)       <= max(ord(Phi)+2, 4).

These counts refer to the input actually passed to localization. If the
optional preprocessing below changes Phi to Phi0, use Phi0's L,V,s,h.

AXIOM-THEORY EQUIVALENCE
-----------------------
Under Gamma, replacing a positive occurrence x by p with x->p, or a
negative occurrence x by n with n->x, increases the formula in the IL
implication order. Induction on the formula therefore proves

    IL |- Gamma -> Phi -> BODY.

Every query follows from Gamma by composing n->x and x->p. Hence
IL+Phi proves F(Phi). In the reverse direction substitute every port,
including every dummy, by its hub x, and substitute D by Phi. All guards
and queries become reflexivities. The substituted continuation is
Phi -> (reflexivities) -> Phi, an IL theorem, so F(Phi) yields Phi.
Thus IL+F(Phi)=IL+Phi. In particular F(Phi) is CL valid when Phi is.

EXACT ATOMIC LOCALIZATION THEOREM
-------------------------------
The only atomic defects of F(Phi) are the partitions that isolate a single
BODY occurrence of a port corresponding to a singleton defect of Phi.
There are no other atomic defects, even when Phi has many larger defects.

Here is a proof, including the dummy-port case.

1. A hub x appears once in each of its guards and nowhere else. A proper
   split of those occurrences partitions the vertices of the bipartite
   query tree. Some tree edge crosses the partition. Assign the two hub
   copies so that its negative endpoint has value 1 and its positive
   endpoint value 0. Set each port to its own guard's hub-copy value.
   Every guard is true and this query is false. With D=0 the continuation
   is true and the whole formula is false.

2. Consider a port split. If some query occurrence is separated from its
   guard occurrence, there is an immediate countervaluation. For a positive
   port set the guard-side copy and all other atoms of Gamma to 1, and the
   separated query-side copy to 0. For a negative port use Gamma all 0 and
   the separated query-side copy 1. A query is false. Set D=0. Therefore
   every valid split must keep every query occurrence with the guard.
   The only occurrence that can remain is its unique BODY occurrence.
   A dummy port has no such occurrence and hence has no valid split.

3. Isolating a BODY port is valid exactly when isolating the corresponding
   source leaf is valid. In one direction, under Gamma the unsplit BODY
   ports are bounded by their hubs in the correct polarities, so Boolean
   monotonicity transfers validity from the split source formula. In the
   other direction, a countervaluation of the split source extends by
   putting all guard-side ports equal to their hubs and the isolated BODY
   copy equal to the source's new variable. All queries are true, BODY is
   false, and D=0 gives a countervaluation of the output split.

4. D has two occurrences. Splitting them is refuted by putting inner D=1,
   outer D=0, and all atoms of Gamma=0. A globally singleton source variable
   still occurs only once in the output and has no proper split.

COMPOUND ABSTRACTIONS: WHAT IS AND IS NOT CLAIMED
-----------------------------------------------
Every CL-valid compound abstraction in F(Phi) abstracts ONE subtree
occurrence lying inside BODY. Moreover, every port leaf inside that subtree
comes from a singleton-defective leaf of Phi. This is a NECESSARY condition;
it is not claimed that every such BODY subtree can be abstracted validly.

To prove it, a valid abstraction can be instantiated back with its removed
subtree while changing selected atom names inside that subtree. It would
then induce an atomic split, to which the exact theorem above applies.
The shapes outside BODY are exhausted by the following cases:

* A guard x->port is unique and contains a hub occurrence. Splitting that
  hub just inside the abstracted guard contradicts hub criticality.
* A query n->p occurs once as a query and possibly once also inside BODY.
  Abstracting the query occurrence, with or without its BODY copy, would
  permit splitting a port at that query occurrence (and, if selected, its
  BODY occurrence). Its guard remains outside, so this is not the permitted
  partition isolating only BODY. Abstracting only the BODY copy is allowed
  by this classification and is considered in the next paragraph.
* A continuation tail is unique and contains inner D but not outer D.
  Instantiating with a fresh D would split D, impossible.
* An outer implication spine is unique and contains both D occurrences.
  Instantiating with just one of its D leaves renamed again splits D.

There are no other repeated compound subtrees: guards use hubs absent from
BODY and queries; terms involving D are unique; all BODY leaf names are
distinct, so each compound BODY subtree occurs there only once. Finally,
abstracting a BODY subtree that contains port u and then reinstating it
with u fresh induces exactly the BODY singleton split. The source leaf of
u must therefore be a singleton defect.

OPTIONAL STAGE 0: CONTRACT PRIVATE SINGLETON SUBTREES
---------------------------------------------------
Before localization, replace every maximal compound subtree all of whose
leaves are globally singleton variables by a fresh atom. Those subtrees are
linear and their variables occur nowhere else. This preprocessing preserves
the pure IL axiom theory, not necessarily pointwise equivalence with the
same original variables. One substitution recovers the old subtree. In the
opposite direction, set its rightmost leaf to the new atom and all other
leaves to top (top can be t->t); the subtree becomes IL equivalent to that
atom. These substitutions fix every variable outside the subtree.

The process preserves, with their natural position mapping, all singleton
defects involving repeated variables. The contracted formula has no compound
subtree consisting exclusively of globally singleton variables. One pass
contracting maximal such subtrees is sufficient.

COROLLARY. If Phi has no singleton defects of repeated variables, applying
stage 0 and then localization gives a FULLY substitution-minimal CL tautology
with the same pure IL axiom theory. Its size is linear in the original size.
Indeed, the atomic theorem excludes all atom splits, and any possible
compound abstraction would have to lie in BODY and contain no port; stage 0
has excluded exactly those remaining purely singleton subtrees.

For arbitrary Phi, localization alone does NOT eliminate its singleton
defects. The following independent selector monitor supplies the missing
axiom-equivalent singleton-essentialization construction.

UNIVERSAL SINGLETON-ESSENTIALIZATION: THE SELECTOR MONITOR
--------------------------------------------------------
Give EVERY syntax-tree node occurrence v its own fresh atom t_v, including
leaf occurrences. Keep the original atom x at each original leaf. Use one
clause per node, according to its polarity in Phi:

    positive internal node: (t_left -> t_right) -> t_v;
    negative internal node: t_v -> t_left -> t_right;
    positive leaf x:         x -> t_v;
    negative leaf x:         t_v -> x.

Call the clauses C_1,...,C_n and the root atom r. Each clause is linear, has
two or three distinct variables, and each of its individual leaves can be
toggled to change its Boolean value in either direction. There are
n=2L-1 clauses and their total leaf count is S=5L-3.

Choose independent fresh selectors x_1,...,x_n, a fresh switch s, and fresh
D. Let Gamma list the following two premises for every i:

    A_i = x_i -> C_i,        B_i = s -> x_i.

The monitor M(Phi) is

    Gamma -> ((s -> r) -> A_1 -> B_1 -> ... -> A_n -> B_n -> D) -> D.

The continuation contains an EXACT QUERY COPY OF EVERY PREMISE, in addition
to the root query s->r. These copies expose a fault in any one premise or
any one query, even when the other gate clauses make the root query redundant.

IL AXIOM EQUIVALENCE. Under all C_i, polarity induction gives B->t_v at a
positive node and t_v->B at a negative node, where B is that node's original
subformula. At an implication node this is composition in the antecedent
and consequent, followed or preceded by its defining clause. Thus under
Gamma and Phi, assuming s yields every x_i, then every C_i, then r.
Consequently s->r is provable, and all remaining continuation arguments are
the Gamma assumptions themselves. This proves IL |- Phi -> M(Phi).

For the converse substitute t_v by the corresponding original subformula,
all x_i and s by top, and D by Phi. Every C_i becomes a reflexivity, hence
every A_i and B_i becomes an IL theorem. The substituted continuation is
(top->Phi)->(IL theorems)->Phi, which is an IL theorem. This substitution
instance of M(Phi) therefore implies Phi. Hence IL+M(Phi)=IL+Phi.

EVERY SINGLE LEAF IS CRITICAL. The following countervaluation schemas cover
all positions of M(Phi); the implementation constructs and scalar-checks
each individual instance. Except for the terminal case, set D=0.

* A data leaf inside C_i in a premise: set s=0, x_i=1, and all other
  selectors 0. Choose the local variables so that the unchanged C_i is
  false and changing just that leaf makes it true. The changed premise is
  true, while its unchanged query copy is false. All other premises hold.
  For a data leaf in a query copy, use C_i true and its changed copy false.

* The selector leaf in A_i: choose C_i=false and s=0. For a premise fault
  let the original x_i=1 and its fresh occurrence=0; for a query fault
  use original x_i=0 and fresh occurrence=1. Other selectors are 0.

* A leaf in the premise B_i=s->x_i: give all data variables value 1, let
  s=1, x_i=0, and all other selectors 1. Alter the selected s occurrence
  to 0 or the selected x_i occurrence to 1. All premises then hold but
  the unchanged query B_i is false.
  For its query's s leaf use s=x_i=0 and fresh s=1; for its query's x_i
  leaf use all data and selectors and s equal to 1 and fresh x_i=0.

* The s leaf in the root query: use s=0, every selector=0, r=0, fresh s=1.
  The r leaf: use all data, selectors, and s equal to 1, with fresh r=0.

* Either D leaf: give all other variables value 1, inner D=1, outer D=0.

In every case all actual premises are true and the continuation is true
(because one query is false, or because inner D=1), while outer D=0.
Thus every singleton split is invalid. The local data-leaf assignments
exist for all four displayed clause types; the code checks at most 16
assignments for each local witness. No large truth table is involved.

The monitor has exactly 22L-8 leaves and 4L+V variables, and order <=5.
Every variable occurs at least twice and in both polarities: each Gamma
leaf has its exact query counterpart with opposite polarity, and D appears
once in each polarity. Therefore no stage-0 contraction or dummy port is
needed when localizing a monitor.

UNIVERSAL MINIMALIZATION THEOREM
------------------------------
For every pure implicational CL tautology Phi, put

    Min(Phi) = F(M(Phi)).

Then Min(Phi) is fully substitution-minimal among CL tautologies and

    IL + Min(Phi) = IL + Phi.

The exact construction counts, before any optional order-4 translation, are

    leaves(Min(Phi))    = 102L - 2V - 38;
    variables(Min(Phi)) = 26L + V - 7;
    ord(Min(Phi))       <= 7.

All compound BODY subtrees in the final localization contain monitor ports,
and all corresponding singleton splits have explicit countervaluations.
The compound classification above therefore excludes every compound
abstraction as well as every atomic split. This is a constructive theorem;
the large constants are bounds for this particular uniform construction,
not claims of shortest size or optimal variable count.

There is also a shorter check of the compound conclusion. In an atom-critical
formula, a valid compound abstraction must abstract a linear PRIVATE subtree:
its variables occur only within the selected copies, and each occurs once
per copy. Otherwise reinstating the subtree with selected leaves renamed
produces a proper valid atomic split. Such a subtree contains a private
atomic pair a->b. The completed construction has no private atomic pair:
each guard pair contains a port with an occurrence elsewhere; each BODY or
query pair uses ports with guard occurrences outside; and the fresh terminal
D is not in an atomic pair. Hence no compound abstraction is valid.

ORDER OPTIMALITY AFTER THE SEPARATE STATMAN STEP. With atoms of order 1,
every CL tautology of order <=3 is already an IL theorem. Indeed, curry it
as A_1->...->A_k->p. Each A_i has order <=2 and is an atomic Horn chain
a_1->...->a_m->b. If p is outside the least forward-chaining closure of
these premises, assigning 1 exactly to that closure is a Boolean
countervaluation. Otherwise forward chaining itself is an IL proof of p
from the premises. Thus for Phi in CL but not IL, an axiom-equivalent
order-4 representative, obtained by the separately assumed Statman step,
has optimal possible order: no order <=3 representative can generate its
axiom theory. For an IL theorem the minimal identity p->p already has
optimal order 2. These order statements do not bound the size of the
unimplemented Statman translation.

FINITE AUDIT AND API
-------------------
Default execution retains the independent localization audit: it enumerates
every binary implication tree with 2,...,6
leaves and every equality partition of its leaf positions, modulo atom
renaming. This is 9,341 inputs, of which 2,533 are CL tautologies. For their
UNPREPROCESSED localized outputs it checks all 70,757 nontrivial atomic
partitions (modulo complement) and 60,989 compound selections. It verifies
the exact atomic classification and the necessary compound classification.
These fixed counts intentionally exclude the separate stage-0 audits and
the named examples Peirce, LC, A4_characteristic, and C3.

For inputs changed by stage 0, a second, separately reported exact audit
checks the preprocessed output, preservation of the number of singleton
defects, and full minimality whenever there are no such defects. Separately,
every one of the 2,533 source tautologies receives a complete monitor
singleton-witness audit. For the four source tautologies with 2 or 3 leaves,
ALL atomic partitions and compound abstractions of the final universally
minimized formula are checked using constructive witnesses, without truth
tables. Larger named examples use the complete monitor singleton audit and
all compound abstractions plus a stated set of representative atomic
partitions. The code does not pretend to enumerate exponentially many hub
partitions for larger outputs: localization_split_witness constructs a
countervaluation for ANY partition supplied by a caller.

Both directions of both IL transformations also have explicit implication-
only lambda terms. An independent small type checker validates the four
closed proof terms on the named examples, including the witness substitutions
needed for the reverse axiom-theory implications. All
countervaluations returned by bitset evaluation, for every operation, are
checked again by an independent scalar Boolean evaluator. A variable-count
guard prevents accidental allocation of enormous truth tables. Assertions
are required: execution under -O/-OO is rejected explicitly.

Useful API:
    arrow(*terms), localize(formula, preprocess_singletons=False),
    contract_private_singleton_subtrees(formula), singleton_defects(formula),
    audit_localization(formula, preprocess_singletons=False),
    boolean_countervaluation(formula), formula_from_json(value),
    selector_monitor(formula), monitor_singleton_witnesses(monitor),
    minimize_classical_tautology(formula, check_tautology=True),
    localization_split_witness(localization, atom, selected, source_witnesses),
    localization_compound_witness(localization, selected_paths, source_witnesses),
    monitor_with_terms(formula), localization_with_terms(formula).

localize returns a Localization record with .formula, .core, .guards,
.queries, .body_positions, .source_positions, .body_path, .metrics, and
.contractions. Construction itself does not run exponential checks.

Optional JSON export of a named example's universal minimization:
    python implicational_minimality_localization.py --examples-only \
        --example Peirce --export-json peirce_localization.json

JSON encodes an atom as a string and an implication as a two-element array.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
import hashlib
import json
from pathlib import Path
import sys
from typing import Iterator, Union

if not __debug__:
    raise RuntimeError("Assertions are required; run without -O or -OO.")

Formula = Union[str, tuple["Formula", "Formula"]]
PathTuple = tuple[int, ...]
DEFAULT_MAX_BOOLEAN_VARIABLES = 20
HARD_MAX_BOOLEAN_VARIABLES = 22


def validate_formula(formula: Formula) -> None:
    if isinstance(formula, str):
        if not formula:
            raise ValueError("Atom names must be nonempty strings")
        return
    if not isinstance(formula, tuple) or len(formula) != 2:
        raise TypeError("A formula must be a nonempty str or a binary tuple")
    validate_formula(formula[0])
    validate_formula(formula[1])


def formula_from_json(value: object) -> Formula:
    if isinstance(value, str) and value:
        return value
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return formula_from_json(value[0]), formula_from_json(value[1])
    raise ValueError("Expected an atom string or a two-element formula array")


def arrow(*terms: Formula) -> Formula:
    if not terms:
        raise ValueError("arrow needs at least one term")
    result = terms[-1]
    for term in reversed(terms[:-1]):
        result = term, result
    return result


def leaves(formula: Formula) -> list[str]:
    output: list[str] = []
    pending = [formula]
    while pending:
        term = pending.pop()
        if isinstance(term, str):
            output.append(term)
        else:
            pending.append(term[1])
            pending.append(term[0])
    return output


def order(formula: Formula) -> int:
    if isinstance(formula, str):
        return 1
    return max(order(formula[0]) + 1, order(formula[1]))


def format_formula(formula: Formula) -> str:
    if isinstance(formula, str):
        return formula
    return f"({format_formula(formula[0])} -> {format_formula(formula[1])})"


class FreshNames:
    def __init__(self, used: set[str]):
        self.used = set(used)

    def take(self, stem: str) -> str:
        name = stem
        suffix = 0
        while name in self.used:
            suffix += 1
            name = f"{stem}_{suffix}"
        self.used.add(name)
        return name


def replace_leaves(formula: Formula, selected: set[int], name: str) -> Formula:
    position = 0

    def go(term: Formula) -> Formula:
        nonlocal position
        if isinstance(term, str):
            here = position
            position += 1
            return name if here in selected else term
        return go(term[0]), go(term[1])

    result = go(formula)
    if any(i < 0 or i >= position for i in selected):
        raise ValueError("Selected leaf position is outside the formula")
    return result


def subtree_at(formula: Formula, path: PathTuple) -> Formula:
    for direction in path:
        if isinstance(formula, str) or direction not in (0, 1):
            raise ValueError("Invalid subtree path")
        formula = formula[direction]
    return formula


def evaluate_boolean(formula: Formula, valuation: dict[str, int]) -> bool:
    """Scalar evaluator, independent of the bitset implementation."""
    if isinstance(formula, str):
        return bool(valuation[formula])
    antecedent = evaluate_boolean(formula[0], valuation)
    consequent = evaluate_boolean(formula[1], valuation)
    return (not antecedent) or consequent


@lru_cache(maxsize=8)
def boolean_tables(n: int) -> tuple[int, tuple[int, ...]]:
    if not 0 <= n <= HARD_MAX_BOOLEAN_VARIABLES:
        raise ValueError(f"Truth-table variable count must be at most {HARD_MAX_BOOLEAN_VARIABLES}")
    assignment_count = 1 << n
    all_bits = (1 << assignment_count) - 1
    columns = []
    for j in range(n):
        block = 1 << j
        period_mask = (1 << (2 * block)) - 1
        one_block = ((1 << block) - 1) << block
        columns.append((all_bits // period_mask) * one_block)
    return all_bits, tuple(columns)


def boolean_countervaluation(
    formula: Formula, *, max_variables: int = DEFAULT_MAX_BOOLEAN_VARIABLES
) -> dict[str, int] | None:
    if not 0 <= max_variables <= HARD_MAX_BOOLEAN_VARIABLES:
        raise ValueError(f"max_variables must be between 0 and {HARD_MAX_BOOLEAN_VARIABLES}")
    variables = sorted(set(leaves(formula)))
    if len(variables) > max_variables:
        raise ValueError(
            f"Exact Boolean audit needs {len(variables)} variables, exceeding "
            f"the configured limit {max_variables}; construction needs no truth table"
        )
    all_bits, columns = boolean_tables(len(variables))
    table = dict(zip(variables, columns))

    def evaluate(term: Formula) -> int:
        if isinstance(term, str):
            return table[term]
        return (all_bits ^ evaluate(term[0])) | evaluate(term[1])

    failures = all_bits ^ evaluate(formula)
    if failures == 0:
        return None
    assignment = (failures & -failures).bit_length() - 1
    valuation = {name: (assignment >> j) & 1 for j, name in enumerate(variables)}
    assert evaluate_boolean(formula, valuation) is False, "Scalar witness check failed"
    return valuation


def singleton_defects(formula: Formula) -> set[int]:
    source = leaves(formula)
    counts = Counter(source)
    fresh = FreshNames(set(source)).take("_split")
    return {
        i for i, name in enumerate(source)
        if counts[name] > 1
        and boolean_countervaluation(replace_leaves(formula, {i}, fresh)) is None
    }


def contract_private_singleton_subtrees(formula: Formula) -> tuple[Formula, list[dict]]:
    """Contract maximal compound subtrees with only globally singleton leaves."""
    validate_formula(formula)
    counts = Counter(leaves(formula))
    fresh = FreshNames(set(counts))
    contractions: list[dict] = []

    def go(term: Formula, path: PathTuple = ()) -> Formula:
        if isinstance(term, str):
            return term
        variables = leaves(term)
        if all(counts[name] == 1 for name in variables):
            name = fresh.take("_loc_contract")
            contractions.append({"path": list(path), "subtree": term, "fresh": name})
            return name
        return go(term[0], path + (0,)), go(term[1], path + (1,))

    core = go(formula)
    return core, contractions


@dataclass
class Localization:
    source: Formula
    core: Formula
    formula: Formula
    body: Formula
    guards: tuple[Formula, ...]
    queries: tuple[Formula, ...]
    body_positions: dict[str, int]
    source_positions: dict[str, int]
    body_path: PathTuple
    terminal: str
    metrics: dict[str, int]
    contractions: list[dict]


def localize(formula: Formula, *, preprocess_singletons: bool = False) -> Localization:
    validate_formula(formula)
    if preprocess_singletons:
        core, contractions = contract_private_singleton_subtrees(formula)
    else:
        core, contractions = formula, []
    counts = Counter(leaves(core))
    fresh = FreshNames(set(leaves(formula)) | set(counts))
    groups: dict[str, dict[int, list[str]]] = defaultdict(lambda: {1: [], -1: []})
    guards: list[Formula] = []
    source_positions: dict[str, int] = {}
    position = 0

    def go(term: Formula, polarity: int = 1) -> Formula:
        nonlocal position
        if isinstance(term, str):
            here = position
            position += 1
            if counts[term] == 1:
                return term
            port = fresh.take(f"_loc_p{here}")
            groups[term][polarity].append(port)
            guards.append((term, port) if polarity == 1 else (port, term))
            source_positions[port] = here
            return port
        return go(term[0], -polarity), go(term[1], polarity)

    body = go(core)
    queries: list[Formula] = []
    h = 0
    for hub, sides in groups.items():
        for polarity in (1, -1):
            if not sides[polarity]:
                h += 1
                port = fresh.take("_loc_dummy")
                sides[polarity].append(port)
                guards.append((hub, port) if polarity == 1 else (port, hub))
        positives, negatives = sides[1], sides[-1]
        queries.extend((negative, positives[0]) for negative in negatives)
        queries.extend((negatives[0], positive) for positive in positives[1:])
    terminal = fresh.take("_loc_D")
    output = arrow(*guards, arrow(body, *queries, terminal), terminal)
    offset = 2 * len(guards)
    body_positions = {port: offset + i for port, i in source_positions.items()}
    body_path = (1,) * len(guards) + (0, 0)
    L, V = sum(counts.values()), len(counts)
    s = sum(count == 1 for count in counts.values())
    metrics = {
        "core_leaves": L, "core_variables": V, "singleton_variables": s,
        "unipolar_repeated_variables": h, "guards": len(guards),
        "queries": len(queries), "output_leaves": len(leaves(output)),
        "output_variables": len(set(leaves(output))), "output_order": order(output),
    }
    assert len(guards) == L - s + h
    assert len(queries) == L - V + h
    assert metrics["output_leaves"] == 5 * L - 2 * V - 2 * s + 4 * h + 2
    assert metrics["output_variables"] == L + V - s + h + 1
    assert metrics["output_order"] <= max(order(core) + 2, 4)
    assert len(set(leaves(body))) == L
    assert subtree_at(output, body_path) == body
    return Localization(formula, core, output, body, tuple(guards), tuple(queries),
                        body_positions, source_positions, body_path, terminal,
                        metrics, contractions)


@dataclass
class SelectorMonitor:
    source: Formula
    formula: Formula
    clauses: tuple[Formula, ...]
    selectors: tuple[str, ...]
    root: str
    switch: str
    terminal: str
    leaf_tags: tuple[tuple, ...]
    node_subformulas: dict[str, Formula]
    metrics: dict[str, int]


def selector_monitor(formula: Formula) -> SelectorMonitor:
    """Polar defining clauses, independent selectors, and exact premise queries."""
    validate_formula(formula)
    fresh = FreshNames(set(leaves(formula)))
    clauses: list[Formula] = []
    node_subformulas: dict[str, Formula] = {}

    def go(term: Formula, positive: bool = True) -> str:
        node = fresh.take(f"_mon_node{len(node_subformulas)}")
        node_subformulas[node] = term
        if isinstance(term, str):
            clause = (term, node) if positive else (node, term)
        else:
            a = go(term[0], not positive)
            b = go(term[1], positive)
            clause = ((a, b), node) if positive else arrow(node, a, b)
        clauses.append(clause)
        return node

    root = go(formula)
    selectors = tuple(fresh.take(f"_mon_select{i}") for i in range(len(clauses)))
    switch = fresh.take("_mon_switch")
    terminal = fresh.take("_mon_D")
    gamma: list[Formula] = []
    gamma_tags: list[tuple[str, int]] = []
    for i, clause in enumerate(clauses):
        gamma.extend(((selectors[i], clause), (switch, selectors[i])))
        gamma_tags.extend((("activation", i), ("link", i)))
    output = arrow(*gamma, arrow((switch, root), *gamma, terminal), terminal)
    tags: list[tuple] = []
    for area in ("premise", "query"):
        if area == "query":
            tags.extend((("root_query", 0, 0), ("root_query", 0, 1)))
        for guard, tag in zip(gamma, gamma_tags):
            tags.extend((area, tag, j) for j in range(len(leaves(guard))))
    tags.extend((("terminal", 0, 0), ("terminal", 0, 1)))
    L = len(leaves(formula))
    V = len(set(leaves(formula)))
    metrics = {
        "input_leaves": L, "input_variables": V,
        "definition_clauses": len(clauses), "definition_leaves": sum(len(leaves(c)) for c in clauses),
        "monitor_leaves": len(leaves(output)), "monitor_variables": len(set(leaves(output))),
        "monitor_order": order(output),
    }
    assert len(tags) == 22 * L - 8 == metrics["monitor_leaves"]
    assert metrics["monitor_variables"] == 4 * L + V
    assert len(clauses) == 2 * L - 1
    assert metrics["definition_leaves"] == 5 * L - 3
    assert metrics["monitor_order"] <= 5
    assert all(count >= 2 for count in Counter(leaves(output)).values())
    return SelectorMonitor(formula, output, tuple(clauses), selectors, root, switch,
                           terminal, tuple(tags), node_subformulas, metrics)


def local_clause_assignment(
    clause: Formula, original_value: int, fresh: str,
    changed_position: int | None = None, changed_value: int | None = None,
) -> dict[str, int]:
    """Search at most 16 assignments: each defining clause has <=3 distinct atoms."""
    names = sorted(set(leaves(clause)))
    assert len(names) == len(leaves(clause)) <= 3
    changed = replace_leaves(clause, {changed_position}, fresh) if changed_position is not None else None
    for values in product((0, 1), repeat=len(names)):
        valuation = dict(zip(names, values))
        if evaluate_boolean(clause, valuation) != bool(original_value):
            continue
        for value in (0, 1):
            valuation[fresh] = value
            if changed is None or evaluate_boolean(changed, valuation) == bool(changed_value):
                return valuation
    raise AssertionError((clause, original_value, changed_position, changed_value))


def monitor_singleton_witnesses(monitor: SelectorMonitor) -> dict[int, dict]:
    """Construct and scalar-check a countervaluation for EVERY monitor leaf split."""
    names = set(leaves(monitor.formula))
    fresh = FreshNames(names).take("_mon_split")
    witnesses: dict[int, dict] = {}
    for position, tag in enumerate(monitor.leaf_tags):
        valuation = {name: 0 for name in names}
        valuation[fresh] = 0
        area, kind, j = tag
        if area in ("premise", "query"):
            typ, i = kind
            clause, selector = monitor.clauses[i], monitor.selectors[i]
            if typ == "activation":
                if j == 0:
                    valuation.update(local_clause_assignment(clause, 0, fresh))
                    valuation[selector] = 1 if area == "premise" else 0
                    valuation[fresh] = 0 if area == "premise" else 1
                else:
                    old = 0 if area == "premise" else 1
                    valuation.update(local_clause_assignment(clause, old, fresh, j - 1, 1 - old))
                    valuation[selector] = 1
            elif area == "premise":
                valuation = {name: 1 for name in names}
                valuation[monitor.terminal] = 0
                valuation[selector] = 0
                valuation[fresh] = 0 if j == 0 else 1
            elif j == 0:
                valuation[monitor.switch] = 0
                valuation[selector] = 0
                valuation[fresh] = 1
            else:
                valuation = {name: 1 for name in names}
                valuation[monitor.terminal] = 0
                valuation[fresh] = 0
        elif area == "root_query":
            if j == 0:
                valuation[monitor.switch] = 0
                valuation[monitor.root] = 0
                valuation[fresh] = 1
            else:
                valuation = {name: 1 for name in names}
                valuation[monitor.terminal] = 0
                valuation[fresh] = 0
        else:
            valuation = {name: 1 for name in names}
            valuation[monitor.terminal] = 0 if j == 0 else 1
            valuation[fresh] = 1 if j == 0 else 0
        generalized = replace_leaves(monitor.formula, {position}, fresh)
        assert evaluate_boolean(generalized, valuation) is False, (position, tag)
        witnesses[position] = {"fresh": fresh, "valuation": valuation}
    assert len(witnesses) == monitor.metrics["monitor_leaves"]
    return witnesses


@dataclass
class UniversalMinimization:
    monitor: SelectorMonitor
    localization: Localization

    @property
    def formula(self) -> Formula:
        return self.localization.formula


def minimize_classical_tautology(formula: Formula, *, check_tautology: bool = True) -> UniversalMinimization:
    """Construct a fully substitution-minimal, axiom-equivalent CL tautology.

    The optional CL check is exponential and subject to the truth-table guard.
    Set check_tautology=False only when CL validity is already established.
    """
    if check_tautology and boolean_countervaluation(formula) is not None:
        raise ValueError("The minimization theorem requires a CL tautology")
    monitor = selector_monitor(formula)
    result = localize(monitor.formula)
    L, V = len(leaves(formula)), len(set(leaves(formula)))
    assert result.metrics["singleton_variables"] == 0
    assert result.metrics["unipolar_repeated_variables"] == 0
    assert result.metrics["output_leaves"] == 102 * L - 2 * V - 38
    assert result.metrics["output_variables"] == 26 * L + V - 7
    assert result.metrics["output_order"] <= 7
    return UniversalMinimization(monitor, result)


def localization_split_witness(
    result: Localization, atom: str, selected: set[int], source_witnesses: dict[int, dict],
) -> dict:
    """Polynomial construction of a witness for any specified output partition.

    source_witnesses supplies the source singleton countervaluations (e.g. from
    monitor_singleton_witnesses). No enumeration of all partitions is needed.
    """
    output_leaves = leaves(result.formula)
    occurrences = {i for i, name in enumerate(output_leaves) if name == atom}
    if not selected or not selected < occurrences:
        raise ValueError("selected must be a nonempty proper set of occurrences of atom")
    names = set(output_leaves)
    fresh = FreshNames(names).take("_split")
    valuation = {name: 0 for name in names}
    valuation[fresh] = 0
    hubs = {name for name, count in Counter(leaves(result.core)).items() if count > 1}
    port_info: dict[str, tuple[str, int, int, int]] = {}
    for j, guard in enumerate(result.guards):
        a, b = guard
        if a in hubs:
            port_info[b] = (a, 1, 2*j+1, 2*j)
        else:
            assert b in hubs
            port_info[a] = (b, -1, 2*j, 2*j+1)
    query_start = 2 * len(result.guards) + len(leaves(result.body))

    def label(position: int) -> str:
        return fresh if position in selected else atom

    if atom == result.terminal:
        inner, outer = len(output_leaves)-2, len(output_leaves)-1
        valuation[label(inner)] = 1
        valuation[label(outer)] = 0
    elif atom in hubs:
        for negative, positive in result.queries:
            ni, pi = port_info[negative], port_info[positive]
            if ni[0] == atom and (ni[3] in selected) != (pi[3] in selected):
                valuation[label(ni[3])] = 1
                valuation[label(pi[3])] = 0
                break
        else:
            raise AssertionError("A hub partition did not cut its query tree")
        for port, (hub, _, _, hub_position) in port_info.items():
            valuation[port] = valuation[label(hub_position)] if hub == atom else valuation[hub]
    elif atom in port_info:
        _, polarity, guard_position, _ = port_info[atom]
        separated_query = None
        for j, (negative, positive) in enumerate(result.queries):
            for endpoint, offset in ((negative, 0), (positive, 1)):
                position = query_start + 2*j + offset
                if endpoint == atom and (position in selected) != (guard_position in selected):
                    separated_query = position
                    break
            if separated_query is not None:
                break
        if separated_query is not None:
            baseline = int(polarity == 1)
            valuation = {name: baseline for name in names}
            valuation[result.terminal] = 0
            valuation[label(guard_position)] = baseline
            valuation[label(separated_query)] = 1 - baseline
        else:
            assert atom in result.body_positions
            source_position = result.source_positions[atom]
            certificate = source_witnesses[source_position]
            source_values, source_fresh = certificate["valuation"], certificate["fresh"]
            for name in set(leaves(result.core)):
                valuation[name] = source_values[name]
            for port, (hub, _, _, _) in port_info.items():
                valuation[port] = source_values[hub]
            hub = port_info[atom][0]
            valuation[label(guard_position)] = source_values[hub]
            valuation[label(result.body_positions[atom])] = source_values[source_fresh]
            valuation[result.terminal] = 0
    else:
        raise AssertionError("A singleton input variable has no proper output partition")
    generalized = replace_leaves(result.formula, selected, fresh)
    assert evaluate_boolean(generalized, valuation) is False, (atom, sorted(selected))
    return {"fresh": fresh, "valuation": valuation}


def leaf_paths(formula: Formula) -> list[PathTuple]:
    output: list[PathTuple] = []

    def go(term: Formula, path: PathTuple = ()) -> None:
        if isinstance(term, str):
            output.append(path)
        else:
            go(term[0], path + (0,))
            go(term[1], path + (1,))

    go(formula)
    return output


def path_to_leaf(formula: Formula, position: int) -> PathTuple:
    current = 0
    path: list[int] = []

    def go(term: Formula) -> PathTuple | None:
        nonlocal current
        if isinstance(term, str):
            here = current
            current += 1
            return tuple(path) if here == position else None
        for direction in (0, 1):
            path.append(direction)
            found = go(term[direction])
            path.pop()
            if found is not None:
                return found
        return None

    found = go(formula)
    if found is None:
        raise ValueError("Leaf position is outside the formula")
    return found


def localization_compound_witness(
    result: Localization, selected_paths: set[PathTuple], source_witnesses: dict[int, dict],
) -> dict:
    """Reduce a specified compound abstraction to one certified atomic split."""
    if not selected_paths:
        raise ValueError("Select at least one compound subtree occurrence")
    subtree = subtree_at(result.formula, next(iter(selected_paths)))
    if isinstance(subtree, str) or any(subtree_at(result.formula, path) != subtree for path in selected_paths):
        raise ValueError("Selected occurrences must be equal compound subtrees")
    local_leaves = leaves(subtree)
    hubs = {name for name, count in Counter(leaves(result.core)).items() if count > 1}
    if result.terminal in local_leaves:
        local_position = local_leaves.index(result.terminal)
    elif any(name in hubs for name in local_leaves):
        local_position = next(i for i, name in enumerate(local_leaves) if name in hubs)
    else:
        # In a universally minimized output every BODY leaf is a port.
        local_position = next(i for i, name in enumerate(local_leaves) if name in result.source_positions)
    atom = local_leaves[local_position]
    relative_path = path_to_leaf(subtree, local_position)
    global_index = getattr(result, "_leaf_path_index", None)
    if global_index is None:
        global_index = {path: i for i, path in enumerate(leaf_paths(result.formula))}
        result._leaf_path_index = global_index
    selected_leaves = {global_index[path + relative_path] for path in selected_paths}
    certificate = localization_split_witness(result, atom, selected_leaves, source_witnesses)
    modified_subtree = replace_leaves(subtree, {local_position}, certificate["fresh"])
    new_atom = FreshNames(set(leaves(result.formula))).take("_abstract")
    valuation = {name: certificate["valuation"][name] for name in set(leaves(result.formula))}
    valuation[new_atom] = int(evaluate_boolean(modified_subtree, certificate["valuation"]))

    def replace(term: Formula, path: PathTuple = ()) -> Formula:
        if path in selected_paths:
            return new_atom
        if isinstance(term, str):
            return term
        return replace(term[0], path + (0,)), replace(term[1], path + (1,))

    generalized = replace(result.formula)
    assert evaluate_boolean(generalized, valuation) is False, sorted(selected_paths)
    return {"fresh": new_atom, "valuation": valuation}


# Implication-only natural-deduction certificates and an independent type checker.
# V is a proof variable, L is abstraction, App is application. No logical
# constants, non-implicational connectives, or classical rules occur here.
def substitute(f, sigma):
    if isinstance(f, str):
        return sigma.get(f, f)
    return (substitute(f[0], sigma), substitute(f[1], sigma))


def V(n):
    return ('v', n)


def L(n, typ, body):
    return ('lam', n, typ, body)


def App(t, *xs):
    for x in xs:
        t = ('app', t, x)
    return t


def lams(bindings, t):
    for n, typ in reversed(bindings):
        t = L(n, typ, t)
    return t


def lets(bindings, t):
    for n, value in reversed(bindings):
        t = ('let', n, value, t)
    return t


def check(t, ctx=None):
    ctx = {} if ctx is None else ctx
    tag = t[0]
    if tag == 'v':
        assert t[1] in ctx, ('unbound', t[1])
        return ctx[t[1]]
    if tag == 'lam':
        _, n, typ, body = t
        assert n not in ctx, ('shadowing', n)
        return (typ, check(body, dict(ctx, **{n: typ})))
    if tag == 'app':
        ft = check(t[1], ctx)
        xt = check(t[2], ctx)
        assert isinstance(ft, tuple) and ft[0] == xt, ('application', ft, xt)
        return ft[1]
    assert tag == 'let', ('unknown', tag)
    _, n, value, body = t
    assert n not in ctx, ('shadowing', n)
    typ = check(value, ctx)
    return check(body, dict(ctx, **{n: typ}))


def nodes(t):
    if t[0] == 'v':
        return 1
    if t[0] == 'lam':
        return 1 + nodes(t[3])
    if t[0] == 'app':
        return 1 + nodes(t[1]) + nodes(t[2])
    return 1 + nodes(t[2]) + nodes(t[3])


class Terms:
    def __init__(self, prefix):
        self.prefix = prefix
        self.serial = 0

    def fresh(self):
        self.serial += 1
        return self.prefix + str(self.serial)

    def lam(self, typ, body):
        n = self.fresh()
        return L(n, typ, body(V(n)))

    def let(self, value, body):
        n = self.fresh()
        return ('let', n, value, body(V(n)))


def monitor_with_terms(phi):
    fresh=FreshNames(set(leaves(phi)))
    clauses=[]; node_sub={}
    def flatten(a, positive=True):
        t=fresh.take(f'_mon_node{len(node_sub)}'); node_sub[t]=a
        if isinstance(a,str):
            child=None; c=(a,t) if positive else (t,a)
        else:
            child=(flatten(a[0], not positive),flatten(a[1],positive))
            x,y=child[0]['name'],child[1]['name']
            c=((x,y),t) if positive else arrow(t,x,y)
        i=len(clauses); clauses.append(c)
        return {'source':a,'name':t,'positive':positive,'children':child,'clause':i}
    tree=flatten(phi); r=tree['name']
    xs=[fresh.take(f'_mon_select{i}') for i in range(len(clauses))]
    s=fresh.take('_mon_switch'); d=fresh.take('_mon_D')
    gamma=[]
    for x,c in zip(xs,clauses):gamma.extend([(x,c),(s,x)])
    q0=(s,r); kt=arrow(q0,*gamma,d)
    f=arrow(*gamma,kt,d)
    assert f == selector_monitor(phi).formula
    nt=Terms('proof_monitor_')
    old=nt.fresh(); gs=[nt.fresh() for _ in gamma]; kn=nt.fresh(); sn=nt.fresh()
    cs=[App(V(gs[2*i]), App(V(gs[2*i+1]),V(sn))) for i in range(len(clauses))]
    def polar(t):
        a,z,pos,child,i=t['source'],t['name'],t['positive'],t['children'],t['clause']
        if child is None:return cs[i]
        pl=polar(child[0]); pr=polar(child[1]); x,y=child[0]['name'],child[1]['name']
        if pos:
            return nt.lam(a,lambda fn:App(cs[i],nt.lam(x,lambda arg:App(pr,App(fn,App(pl,arg))))))
        return nt.lam(z,lambda val:nt.lam(a[0],lambda arg:App(pr,App(cs[i],val,App(pl,arg)))))
    qproof=L(sn,s,App(polar(tree),V(old)))
    fw=lams([(old,phi),*zip(gs,gamma),(kn,kt)],App(V(kn),qproof,*[V(g) for g in gs]))
    assert check(fw)==(phi,f)

    top=(fresh.take('_proof_truth'),)*2
    rho={**node_sub,s:top,d:phi,**{x:top for x in xs}}
    fg=substitute(f,rho); transformed_gamma=[substitute(g,rho) for g in gamma]
    true=nt.lam(top[0],lambda p:p)
    gps=[]
    for i,c in enumerate(clauses):
        ct=substitute(c,rho); assert ct[0]==ct[1]
        ident=nt.lam(ct[0],lambda p:p)
        gps.extend([nt.lam(top,lambda p,ident=ident:ident),nt.lam(top,lambda p:p)])
    qn=nt.fresh(); ignored=[nt.fresh() for _ in gamma]
    kp=lams([(qn,(top,phi)),*zip(ignored,transformed_gamma)],App(V(qn),true))
    fn=nt.fresh(); bw=L(fn,fg,App(V(fn),*gps,kp))
    assert check(bw)==(fg,phi)
    return f,fw,bw,rho

def localization_with_terms(a):
    z=localize(a); nt=Terms('proof_localize_')
    gamma=list(z.guards); gs=[nt.fresh() for _ in gamma]
    guardproof={g:V(n) for g,n in zip(gamma,gs)}
    old=nt.fresh();kn=nt.fresh()
    def variance(src,dst,positive=True):
        if isinstance(src,str):
            if src==dst:return nt.lam(src,lambda p:p)
            return guardproof[(src,dst) if positive else (dst,src)]
        pl=variance(src[0],dst[0],not positive)
        pr=variance(src[1],dst[1],positive)
        typ=src if positive else dst
        inp=dst[0] if positive else src[0]
        return nt.lam(typ,lambda fn:nt.lam(inp,lambda p:App(pr,App(fn,App(pl,p)))))
    qproof=[]
    hubs=set(leaves(a))
    for n,p in z.queries:
        options=[x for x in hubs if (n,x) in guardproof and (x,p) in guardproof]
        assert len(options)==1
        x=options[0]
        qproof.append(nt.lam(n,lambda arg,x=x,n=n,p=p:App(guardproof[(x,p)],App(guardproof[(n,x)],arg))))
    kt=arrow(z.body,*z.queries,z.terminal)
    fw=lams([(old,a),*zip(gs,gamma),(kn,kt)],App(V(kn),App(variance(a,z.body),V(old)),*qproof))
    assert check(fw)==(a,z.formula)
    rho={z.terminal:a}
    for l,r in gamma:
        if l in hubs:rho[r]=l
        else:
            assert r in hubs;rho[l]=r
    fg=substitute(z.formula,rho)
    gps=[]
    for g in gamma:
        ct=substitute(g,rho);assert ct[0]==ct[1]
        gps.append(nt.lam(ct[0],lambda p:p))
    bn=nt.fresh();rns=[nt.fresh() for _ in z.queries]
    kp=lams([(bn,a),*zip(rns,[substitute(q,rho) for q in z.queries])],V(bn))
    fn=nt.fresh();bw=L(fn,fg,App(V(fn),*gps,kp))
    assert check(bw)==(fg,a)
    return z,fw,bw,rho


def atom_splits(formula: Formula) -> Iterator[tuple[dict, Formula]]:
    occurrences: dict[str, list[int]] = defaultdict(list)
    for i, name in enumerate(leaves(formula)):
        occurrences[name].append(i)
    fresh = FreshNames(set(occurrences)).take("_split")
    for name, positions in occurrences.items():
        # Keep the last occurrence fixed: enumerate one of each complementary pair.
        for mask in range(1, 1 << (len(positions) - 1)):
            selected = {positions[j] for j in range(len(positions) - 1) if mask & (1 << j)}
            yield {"atom": name, "leaf_positions": sorted(selected)}, replace_leaves(formula, selected, fresh)


def compound_abstractions(formula: Formula) -> Iterator[tuple[dict, Formula]]:
    occurrences: dict[Formula, list[PathTuple]] = defaultdict(list)

    def collect(term: Formula, path: PathTuple = ()) -> None:
        if isinstance(term, str):
            return
        occurrences[term].append(path)
        collect(term[0], path + (0,))
        collect(term[1], path + (1,))

    collect(formula)
    fresh = FreshNames(set(leaves(formula))).take("_abstract")
    for subtree, paths in occurrences.items():
        for mask in range(1, 1 << len(paths)):
            selected = {paths[j] for j in range(len(paths)) if mask & (1 << j)}

            def replace(term: Formula, path: PathTuple = ()) -> Formula:
                if path in selected:
                    return fresh
                if isinstance(term, str):
                    return term
                return replace(term[0], path + (0,)), replace(term[1], path + (1,))

            yield {"subtree": subtree, "paths": sorted(selected)}, replace(formula)


def audit_localization(formula: Formula, *, preprocess_singletons: bool = False) -> dict[str, int | bool]:
    if boolean_countervaluation(formula) is not None:
        raise ValueError("Localization audit expects a CL tautology")
    result = localize(formula, preprocess_singletons=preprocess_singletons)
    assert boolean_countervaluation(result.core) is None
    assert boolean_countervaluation(result.formula) is None
    expected = singleton_defects(result.core)
    if preprocess_singletons:
        assert len(singleton_defects(formula)) == len(expected)
        repeated = {name for name, count in Counter(leaves(result.core)).items() if count > 1}
        for operation, _ in compound_abstractions(result.core):
            assert any(name in repeated for name in leaves(operation["subtree"]))
    occurrences: dict[str, set[int]] = defaultdict(set)
    for i, name in enumerate(leaves(result.formula)):
        occurrences[name].add(i)
    actual: set[int] = set()
    partitions = compounds = valid_compounds = 0
    for operation, generalized in atom_splits(result.formula):
        partitions += 1
        if boolean_countervaluation(generalized) is None:
            name = operation["atom"]
            selected = set(operation["leaf_positions"])
            assert name in result.body_positions, (formula, operation)
            body_singleton = {result.body_positions[name]}
            assert selected == body_singleton or occurrences[name] - selected == body_singleton, (formula, operation)
            actual.add(result.source_positions[name])
    assert actual == expected, (format_formula(formula), actual, expected)
    for operation, generalized in compound_abstractions(result.formula):
        compounds += 1
        if boolean_countervaluation(generalized) is None:
            valid_compounds += 1
            assert len(operation["paths"]) == 1, (formula, operation)
            path = operation["paths"][0]
            assert path[:len(result.body_path)] == result.body_path, (formula, operation)
            for port in leaves(subtree_at(result.formula, path)):
                if port in result.source_positions:
                    assert result.source_positions[port] in expected, (formula, operation, port)
    minimal = not actual and valid_compounds == 0
    if preprocess_singletons and not expected:
        assert minimal, "The singleton-critical corollary failed"
    return {
        "input_leaves": len(leaves(formula)), **result.metrics,
        "stage0_contractions": len(result.contractions),
        "singleton_defects": len(expected), "atom_partitions_checked": partitions,
        "compound_selections_checked": compounds, "valid_compound_selections": valid_compounds,
        "fully_minimal": minimal,
    }


@lru_cache(maxsize=None)
def binary_shapes(n: int) -> tuple:
    if n == 1:
        return (None,)
    return tuple((a, b) for k in range(1, n) for a in binary_shapes(k) for b in binary_shapes(n-k))


def equality_partitions(n: int, prefix: tuple[int, ...] = (0,)) -> Iterator[tuple[int, ...]]:
    if len(prefix) == n:
        yield prefix
        return
    for label in range(max(prefix) + 2):
        yield from equality_partitions(n, prefix + (label,))


def populate(shape: object, labels: tuple[int, ...]) -> Formula:
    names = iter(labels)

    def go(node: object) -> Formula:
        if node is None:
            return f"x{next(names)}"
        return go(node[0]), go(node[1])

    return go(shape)


def named_examples() -> dict[str, Formula]:
    a, b, c, o = "a", "b", "c", "o"
    return {
        "Peirce": arrow(arrow(arrow(a, b), a), a),
        "LC": arrow(arrow(arrow(a, b), c), arrow(arrow(b, a), c), c),
        "A4_characteristic": arrow(arrow(arrow(a, b), b), arrow(arrow(b, a), a), arrow(a, o), arrow(b, o), o),
        "C3": arrow(arrow(a, b), arrow(b, c), arrow(arrow(b, a), a), arrow(arrow(c, b), b), c),
    }


def representative_partitions(formula: Formula) -> Iterator[tuple[str, set[int]]]:
    occurrences: dict[str, list[int]] = defaultdict(list)
    for i, name in enumerate(leaves(formula)):
        occurrences[name].append(i)
    for name, positions in occurrences.items():
        whole = set(positions)
        candidates = [{position} for position in positions]
        candidates.extend(set(positions[:k]) for k in range(1, len(positions)))
        candidates.append(set(positions[::2]))
        seen: set[frozenset[int]] = set()
        for selected in candidates:
            if positions[-1] in selected:
                selected = whole - selected
            key = frozenset(selected)
            if selected and key not in seen:
                seen.add(key)
                yield name, selected


def audit_universal_construction(formula: Formula, *, all_partitions: bool) -> dict:
    result = minimize_classical_tautology(formula)
    source_witnesses = monitor_singleton_witnesses(result.monitor)
    localized = result.localization
    partition_count = 0
    if all_partitions:
        for operation, generalized in atom_splits(result.formula):
            certificate = localization_split_witness(
                localized, operation["atom"], set(operation["leaf_positions"]), source_witnesses
            )
            assert evaluate_boolean(generalized, certificate["valuation"]) is False
            partition_count += 1
    else:
        for atom, selected in representative_partitions(result.formula):
            localization_split_witness(localized, atom, selected, source_witnesses)
            partition_count += 1
    compound_count = 0
    for operation, generalized in compound_abstractions(result.formula):
        certificate = localization_compound_witness(localized, set(operation["paths"]), source_witnesses)
        assert evaluate_boolean(generalized, certificate["valuation"]) is False
        compound_count += 1
    return {
        **result.monitor.metrics,
        "final_leaves": localized.metrics["output_leaves"],
        "final_variables": localized.metrics["output_variables"],
        "final_order": localized.metrics["output_order"],
        "monitor_singleton_witnesses": len(source_witnesses),
        "atomic_partition_mode": "all" if all_partitions else "singletons_prefixes_alternating",
        "atomic_partition_witnesses": partition_count,
        "all_compound_selection_witnesses": compound_count,
    }


def audit_il_proofs(formula: Formula) -> dict[str, list[int]]:
    previous_limit = sys.getrecursionlimit()
    try:
        sys.setrecursionlimit(max(previous_limit, 10000))
        monitor, forward, backward, _ = monitor_with_terms(formula)
        localized, forward2, backward2, _ = localization_with_terms(monitor)
        expected = minimize_classical_tautology(formula, check_tautology=False)
        assert monitor == expected.monitor.formula
        assert localized.formula == expected.formula
        return {"checked_IL_proof_term_nodes": [nodes(term) for term in (forward, backward, forward2, backward2)]}
    finally:
        sys.setrecursionlimit(previous_limit)


def run_exhaustive_audit() -> tuple[Counter, Counter]:
    total: Counter = Counter()
    stage0: Counter = Counter()
    monitors: Counter = Counter()
    universal_small: Counter = Counter()
    for n in range(2, 7):
        layer: Counter = Counter()
        for shape in binary_shapes(n):
            for labels in equality_partitions(n):
                formula = populate(shape, labels)
                layer["inputs"] += 1
                if boolean_countervaluation(formula) is not None:
                    continue
                layer["tautologies"] += 1
                report = audit_localization(formula)
                monitor = selector_monitor(formula)
                monitor_witnesses = monitor_singleton_witnesses(monitor)
                monitors["tautological_inputs"] += 1
                monitors["all_monitor_singleton_witnesses"] += len(monitor_witnesses)
                if n <= 3:
                    complete = audit_universal_construction(formula, all_partitions=True)
                    universal_small["tautological_inputs"] += 1
                    universal_small["all_atomic_partition_witnesses"] += complete["atomic_partition_witnesses"]
                    universal_small["all_compound_selection_witnesses"] += complete["all_compound_selection_witnesses"]
                for key in ("atom_partitions_checked", "compound_selections_checked", "singleton_defects"):
                    layer[key] += report[key]
                core, contractions = contract_private_singleton_subtrees(formula)
                if contractions:
                    assert core != formula
                    extra = audit_localization(formula, preprocess_singletons=True)
                    stage0["changed_inputs"] += 1
                    stage0["contractions"] += len(contractions)
                    for key in ("atom_partitions_checked", "compound_selections_checked"):
                        stage0[key] += extra[key]
                    stage0["singleton_critical_inputs"] += extra["singleton_defects"] == 0
                    stage0["fully_minimal_outputs"] += extra["fully_minimal"]
        total.update(layer)
        print(json.dumps({"unpreprocessed_leaves": n, **layer}), flush=True)
    expected = {"inputs": 9341, "tautologies": 2533, "atom_partitions_checked": 70757, "compound_selections_checked": 60989}
    for key, value in expected.items():
        assert total[key] == value, (key, total[key], value)
    print(json.dumps({"UNPREPROCESSED_TOTAL": dict(total)}), flush=True)
    print(json.dumps({"SEPARATE_STAGE0_AUDIT": dict(stage0)}), flush=True)
    print(json.dumps({"MONITOR_SINGLETON_AUDIT": dict(monitors)}), flush=True)
    print(json.dumps({"UNIVERSAL_COMPLETE_OPERATIONS_SOURCE_LEAVES_2_TO_3": dict(universal_small)}), flush=True)
    return total, stage0


def audit_fresh_names() -> None:
    a, b = "_loc_D", "_loc_p0"
    colliding = arrow(arrow(arrow(a, b), a), a)
    audit_localization(colliding, preprocess_singletons=True)
    private = arrow(("_loc_contract", "_loc_dummy"), "_split", "_split")
    audit_localization(private, preprocess_singletons=True)
    colliding_monitor = arrow(arrow(arrow("_mon_D", "_mon_node0"), "_mon_D"), "_mon_D")
    monitor_singleton_witnesses(selector_monitor(colliding_monitor))
    audit_il_proofs(colliding_monitor)
    assert formula_from_json(json.loads(json.dumps(colliding))) == colliding
    too_many = arrow(*(f"guard_atom_{i}" for i in range(DEFAULT_MAX_BOOLEAN_VARIABLES + 1)))
    try:
        boolean_countervaluation(too_many)
    except ValueError:
        pass
    else:
        raise AssertionError("Boolean variable-count guard failed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    parser.add_argument("--examples-only", action="store_true", help="Skip the exhaustive 2-to-6-leaf audit")
    parser.add_argument("--example", choices=tuple(named_examples()), default="Peirce", help="Named formula used for optional JSON export")
    parser.add_argument("--export-json", type=Path, help="Export the selected example's universal minimization")
    args = parser.parse_args()
    if not args.examples_only:
        run_exhaustive_audit()
    for name, formula in named_examples().items():
        print(json.dumps({"named_example": name, "preprocess_singletons": True, **audit_localization(formula, preprocess_singletons=True)}), flush=True)
        print(json.dumps({"universal_named_example": name, **audit_universal_construction(formula, all_partitions=False), **audit_il_proofs(formula)}), flush=True)
    width3 = arrow(*[((f"x{i}", f"x{j}"), "z") for i in range(3) for j in range(3) if i != j], "z")
    print(json.dumps({"universal_named_example": "W3", **audit_universal_construction(width3, all_partitions=False), **audit_il_proofs(width3)}), flush=True)
    audit_fresh_names()
    if args.export_json is not None:
        result = minimize_classical_tautology(named_examples()[args.example])
        payload = {"name": args.example, "input": result.monitor.source,
                   "monitor": result.monitor.formula, "formula": result.formula,
                   "monitor_metrics": result.monitor.metrics,
                   "final_metrics": result.localization.metrics,
                   "order4_translation_implemented": False}
        args.export_json.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"exported_json": str(args.export_json)}), flush=True)
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps({"status": "PASS", "sha256": digest, "scalar_countervaluation_checks": "all returned witnesses", "Statman_translation": "not implemented"}), flush=True)


if __name__ == "__main__":
    main()
