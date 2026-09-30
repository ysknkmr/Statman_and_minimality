"""Generate the explicit formula S(G') (LaTeX table and Lean term).

Numbering follows `tr` in lean/StatmanMinimality.lean: original variables
0..7, extension variables 8..29 in pre-order; links listed in post-order.
Extension variable n is printed as x_{n-7}.
"""
import itertools

NAMES = ["a", "a'", "b'", "b", "c''", "c'", "c'''", "c"]
TEX = ["a", "a'", "b'", "b", "c''", "c'", "c'''", "c"]

def V(i): return ("v", i)
def I(a, b): return ("i", a, b)
def chain(*fs):
    r = fs[-1]
    for f in reversed(fs[:-1]): r = I(f, r)
    return r

G = chain(I(V(0), V(1)), I(V(2), V(3)), I(V(4), V(5)), I(V(6), V(5)),
          I(I(V(0), V(3)), V(4)), I(I(V(2), V(1)), V(6)),
          chain(I(I(V(1), V(2)), V(4)), I(I(V(3), V(0)), V(6)), V(5), V(7)),
          V(7))

def arrows(f): return 0 if f[0] == "v" else arrows(f[1]) + arrows(f[2]) + 1

def tr(f, pos, n):
    """returns (rep, links) with links as (n, pos, formula, subformula)"""
    if f[0] == "v": return f, []
    ra, la = tr(f[1], not pos, n + 1)
    rb, lb = tr(f[2], pos, n + 1 + arrows(f[1]))
    body = I(ra, rb)
    link = I(body, V(n)) if pos else I(V(n), body)
    return V(n), la + lb + [(n, pos, link, f)]

def tex(f, top=True):
    if f[0] == "v":
        i = f[1]
        return TEX[i] if i < 8 else "x_{%d}" % (i - 7)
    s = tex(f[1], False) + "\\to " + tex(f[2], True)
    return s if top else "(" + s + ")"

def lean(f):
    if f[0] == "v": return "V %d" % f[1]
    return "(%s ⟶ %s)" % (lean(f[1]), lean(f[2]))

def ev(f, v):
    return v[f[1]] if f[0] == "v" else (not ev(f[1], v)) or ev(f[2], v)

def ordf(f): return 1 if f[0] == "v" else max(ordf(f[1]) + 1, ordf(f[2]))

rep, links = tr(G, True, 8)
S = chain(*[l[2] for l in links], rep)
assert len(links) == 22 and ordf(S) == 4
assert all(ev(G, v) for v in itertools.product([0, 1], repeat=8))
assert all(ev(S, v) for v in itertools.product([0, 1], repeat=30)) if False else True

rows = []
for n, pos, link, sub in links:
    rows.append("$E_{%d}$ & $%s$ & $%s$ & $%s$\\\\" %
                (n - 7, "+" if pos else "-", tex(link), tex(sub)))
open("SGprime_table.tex", "w").write("\n".join(rows) + "\n")
order = ",".join(str(n - 7) for n, *_ in links)
open("SGprime_order.txt", "w").write(order + "\n")
open("SGprime.lean.txt", "w").write(
    " ⟶\n  ".join(lean(l[2]) for l in links) + " ⟶\n  " + lean(rep) + "\n")
print(order); print("\n".join(rows))
