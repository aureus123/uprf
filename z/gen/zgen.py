"""Boilerplate generator for the Z/EVES development: a one-argument function given by an
explicit formula, with its consistency theorem (witness, typing, values, existence)."""

def ufun(name, short, body, var='x', label=None, comment=None):
    """funNAME : nat -> nat with rule SHORTVal: funNAME var = body."""
    label = label or short + 'Val'
    w = short + 'Wit'
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{axdef}}
  {name}: \nat \fun \nat
\where
  \Label{{rule {label}}} \forall {var}: \nat @ {name}~{var} = {body}
\end{{axdef}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{zed}}
  {w} == (\lambda {var}: \nat @ {body})
\end{{zed}}

\begin{{theorem}}{{{w}Fun}}
  {w} \in \nat \fun \nat
\end{{theorem}}

\begin{{zproof}}
invoke {w};
apply FunIntro to predicate (\lambda {var}: \nat @ {body}) \in \nat \fun \nat;
prove by reduce;
with enabled (RelPow) prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{rule {w}Val}}
  \forall {var}: \nat @ {w}~{var} = {body}
\end{{theorem}}

\begin{{zproof}}
prove;
use {w}Fun;
use pairInFunction[\nat, \nat][f := {w}, x := {var}, y := {body}];
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{{short}Ex}}
  \exists {name}: \nat \fun \nat @ \forall {var}: \nat @ {name}~{var} = {body}
\end{{theorem}}

\begin{{zproof}}
instantiate {name} == {w};
use {w}Fun;
prove;
\end{{zproof}}
"""

def ufun_wit(name, short, body, wit, var='x', label=None, comment=None):
    """Like ufun, but with an explicit witness term WIT whose type and values Z/EVES proves by
    reduction (e.g. a constant function overridden at finitely many points)."""
    label = label or short + 'Val'
    w = short + 'Wit'
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{axdef}}
  {name}: \nat \fun \nat
\where
  \Label{{rule {label}}} \forall {var}: \nat @ {name}~{var} = {body}
\end{{axdef}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{zed}}
  {w} == {wit}
\end{{zed}}

\begin{{theorem}}{{{w}Fun}}
  {w} \in \nat \fun \nat
\end{{theorem}}

\begin{{zproof}}
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{rule {w}Val}}
  \forall {var}: \nat @ {w}~{var} = {body}
\end{{theorem}}

\begin{{zproof}}
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{{short}Ex}}
  \exists {name}: \nat \fun \nat @ \forall {var}: \nat @ {name}~{var} = {body}
\end{{theorem}}

\begin{{zproof}}
instantiate {name} == {w};
use {w}Fun;
prove;
\end{{zproof}}
"""

UF = r'\nat \fun \nat'
UOP = r'(\nat \fun \nat) \fun (\nat \fun \nat)'
BOP = r'(\nat \fun \nat) \cross (\nat \fun \nat) \fun (\nat \fun \nat)'

def uop(name, short, body, label=None, comment=None, extra_inner=''):
    """opNAME : (N->N) -> (N->N) with rule SHORTVal: opNAME F x = body (in F, x)."""
    label = label or short + 'Val'
    w = short + 'Wit'
    lam = rf'(\lambda x: \nat @ {body})'
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{axdef}}
  {name}: {UOP}
\where
  \Label{{rule {label}}} \forall F: {UF}; x: \nat @ {name}~F~x = {body}
\end{{axdef}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {short}Inner}}
  \forall F: {UF} @ {lam} \in {UF}
\end{{theorem}}

\begin{{zproof}}
apply FunIntro to predicate {lam} \in {UF};
with enabled (RelPow, inPower) prove by reduce;{extra_inner}
\end{{zproof}}

\begin{{zed}}
  {w} == (\lambda F: {UF} @ {lam})
\end{{zed}}

\begin{{zproof}}[{w}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{{w}Fun}}
  {w} \in {UOP}
\end{{theorem}}

\begin{{zproof}}
invoke {w};
apply FunIntro to predicate (\lambda F: {UF} @ {lam}) \in {UOP};
with enabled (RelPow, inPower) prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{{w}App}}
  \forall F: {UF} @ {w}~F = {lam}
\end{{theorem}}

\begin{{zproof}}
use {w}Fun;
use pairInFunction[{UF}, {UF}][f := {w}, x := F, y := {lam}];
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{rule {w}Val}}
  \forall F: {UF}; x: \nat @ {w}~F~x = {body}
\end{{theorem}}

\begin{{zproof}}
prove;
use {w}App[F := F];
use pairInFunction[\nat, \nat][f := {lam}, x := x, y := {body}];
prove;
\end{{zproof}}

\begin{{theorem}}{{{short}Ex}}
  \exists {name}: {UOP} @ \forall F: {UF}; x: \nat @ {name}~F~x = {body}
\end{{theorem}}

\begin{{zproof}}
instantiate {name} == {w};
use {w}Fun;
prove;
\end{{zproof}}
"""


def bop(name, short, body, label=None, comment=None, extra_inner=''):
    """opNAME : (N->N) x (N->N) -> (N->N) with rule SHORTVal: opNAME(F, G) x = body."""
    label = label or short + 'Val'
    w = short + 'Wit'
    lam = rf'(\lambda x: \nat @ {body})'
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{axdef}}
  {name}: {BOP}
\where
  \Label{{rule {label}}} \forall F, G: {UF}; x: \nat @ {name}(F, G)~x = {body}
\end{{axdef}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {short}Inner}}
  \forall F, G: {UF} @ {lam} \in {UF}
\end{{theorem}}

\begin{{zproof}}
apply FunIntro to predicate {lam} \in {UF};
with enabled (RelPow, inPower) prove by reduce;{extra_inner}
\end{{zproof}}

\begin{{zed}}
  {w} == (\lambda F, G: {UF} @ {lam})
\end{{zed}}

\begin{{zproof}}[{w}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{{w}Fun}}
  {w} \in {BOP}
\end{{theorem}}

\begin{{zproof}}
invoke {w};
apply FunIntro to predicate (\lambda F, G: {UF} @ {lam}) \in {BOP};
with enabled (RelPow, inPower) prove by reduce;
instantiate F == x.1, G == x.2;
prove;
\end{{zproof}}

\begin{{theorem}}{{{w}App}}
  \forall F, G: {UF} @ {w}(F, G) = {lam}
\end{{theorem}}

\begin{{zproof}}
use {w}Fun;
use pairInFunction[({UF}) \cross ({UF}), {UF}][f := {w}, x := (F, G), y := {lam}];
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{rule {w}Val}}
  \forall F, G: {UF}; x: \nat @ {w}(F, G)~x = {body}
\end{{theorem}}

\begin{{zproof}}
prove;
use {w}App[F := F, G := G];
use pairInFunction[\nat, \nat][f := {lam}, x := x, y := {body}];
prove;
\end{{zproof}}

\begin{{theorem}}{{{short}Ex}}
  \exists {name}: {BOP} @ \forall F, G: {UF}; x: \nat @ {name}(F, G)~x = {body}
\end{{theorem}}

\begin{{zproof}}
instantiate {name} == {w};
use {w}Fun;
prove;
\end{{zproof}}
"""

def member(name, expr, eqthm, closure='C6'):
    """NAME: the function computed by EXPR (equation EQTHM) is in CLOSURE."""
    return rf"""\begin{{theorem}}{{{name}Expr}}
  {expr} \in {closure}
\end{{theorem}}

\begin{{zproof}}
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {name}}}
  {eqthm[1]} \in {closure}
\end{{theorem}}

\begin{{zproof}}
use {name}Expr;
use {eqthm[0]};
prove;
\end{{zproof}}
"""

def induct(name, var, pred, base, step, comment=None):
    """Induction on var over N for predicate PRED (in VAR): the set NAMESet, its base and step
    lemmas (rules, proved by the scripts BASE and STEP after invoking the set), and NAMEAll:
    for all var: nat @ PRED."""
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{zed}}
  {name}Set == \{{ {var}: \nat | {pred} \}}
\end{{zed}}

\begin{{zproof}}[{name}Set\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {name}Base}}
  0 \in {name}Set
\end{{theorem}}

\begin{{zproof}}
invoke {name}Set;
{base}
\end{{zproof}}

\begin{{theorem}}{{rule {name}Step}}
  \forall {var}: {name}Set @ 1 + {var} \in {name}Set
\end{{theorem}}

\begin{{zproof}}
invoke {name}Set;
{step}
\end{{zproof}}

\begin{{theorem}}{{{name}Sub}}
  \nat \subseteq {name}Set
\end{{theorem}}

\begin{{zproof}}
apply natInduction to predicate \nat \subseteq {name}Set;
prove;
invoke {name}Set;
prove;
\end{{zproof}}

\begin{{theorem}}{{{name}All}}
  \forall {var}: \nat @ {pred}
\end{{theorem}}

\begin{{zproof}}
prove;
use {name}Sub;
invoke {name}Set;
with enabled (inPower) prove;
instantiate e == {var};
prove;
\end{{zproof}}
"""

def exprop1(name, body, comment=None):
    """An expression of the paper with one function parameter F, as an abbreviation
    NAME == (lambda F: N->N @ BODY), with its typing lemma NAMEFun and the (disabled)
    unfolding rule NAMEApp."""
    c = (comment + '\n\n') if comment else ''
    lam = rf'(\lambda F: {UF} @ {body})'
    return rf"""{c}\begin{{zed}}
  {name} == {lam}
\end{{zed}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {name}Fun}}
  {name} \in {UOP}
\end{{theorem}}

\begin{{zproof}}
invoke {name};
apply FunIntro to predicate {lam} \in {UOP};
with enabled (RelPow, inPower) prove by reduce;
\end{{zproof}}

\begin[disabled]{{theorem}}{{rule {name}App}}
  \forall F: {UF} @ {name}~F = {body}
\end{{theorem}}

\begin{{zproof}}
use {name}Fun;
use pairInFunction[{UF}, {UF}][f := {name}, x := F, y := {body}];
invoke {name};
prove by reduce;
\end{{zproof}}
"""

def exprop2(name, body, comment=None):
    """Like exprop1, with two function parameters F, G (NAME applied to the pair (F, G))."""
    c = (comment + '\n\n') if comment else ''
    lam = rf'(\lambda F, G: {UF} @ {body})'
    return rf"""{c}\begin{{zed}}
  {name} == {lam}
\end{{zed}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {name}Fun}}
  {name} \in {BOP}
\end{{theorem}}

\begin{{zproof}}
invoke {name};
apply FunIntro to predicate {lam} \in {BOP};
with enabled (RelPow, inPower) prove;
instantiate F == x.1, G == x.2;
prove;
\end{{zproof}}

\begin[disabled]{{theorem}}{{rule {name}App}}
  \forall F, G: {UF} @ {name}(F, G) = {body}
\end{{theorem}}

\begin{{zproof}}
use {name}Fun;
use pairInFunction[({UF}) \cross ({UF}), {UF}][f := {name}, x := (F, G), y := {body}];
invoke {name};
prove by reduce;
\end{{zproof}}
"""

def ufun_nonneg(name, short, body, facts, comment=None):
    """funNAME : N -> N given by an integer-valued formula BODY whose nonnegativity follows from
    the FACTS (a list of 'use' instances in x); the value rule is disabled."""
    w = short + 'Wit'
    lam = rf'(\lambda x: \nat @ {body})'
    uses = "\n".join(f"use {f};" for f in facts)
    c = (comment + '\n\n') if comment else ''
    return rf"""{c}\begin{{axdef}}
  {name}: \nat \fun \nat
\where
  \Label{{disabled rule {short}Val}} \forall x: \nat @ {name}~x = {body}
\end{{axdef}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin{{zed}}
  {w} == {lam}
\end{{zed}}

\begin{{zproof}}[{w}\$domainCheck]
prove;
\end{{zproof}}

\begin{{theorem}}{{{w}Rel}}
  {lam} \in \power (\nat \cross \nat)
\end{{theorem}}

\begin{{zproof}}
with enabled (inPower) prove by reduce;
{uses}
prove;
\end{{zproof}}

\begin{{theorem}}{{{w}Fun}}
  {w} \in \nat \fun \nat
\end{{theorem}}

\begin{{zproof}}
invoke {w};
use {w}Rel;
apply FunIntro to predicate {lam} \in \nat \fun \nat;
with enabled (RelPow) prove by reduce;
{uses}
prove;
\end{{zproof}}

\begin{{theorem}}{{rule {w}Val}}
  \forall x: \nat @ {w}~x = {body}
\end{{theorem}}

\begin{{zproof}}
prove;
use {w}Fun;
use pairInFunction[\nat, \nat][f := {w}, x := x, y := {body}];
invoke {w};
prove by reduce;
\end{{zproof}}

\begin{{theorem}}{{{short}Ex}}
  \exists {name}: \nat \fun \nat @ \forall x: \nat @ {name}~x = {body}
\end{{theorem}}

\begin{{zproof}}
instantiate {name} == {w};
use {w}Fun;
prove;
\end{{zproof}}
"""

def closure(name, inits, unops, binops, comment=None):
    """A named closure NAME == clos {inits} {unops} {binops}, kept folded, with its typing
    lemmas and one membership rule per initial function and operator."""
    I = r'\{ ' + ', '.join(inits) + r' \}'
    U = r'\{ ' + ', '.join(unops) + r' \}'
    B = r'\{ ' + ', '.join(binops) + r' \}'
    c = (comment + '\n\n') if comment else ''
    out = [rf"""{c}\begin{{zed}}
  {name} == clos~{I}~{U}~{B}
\end{{zed}}

\begin{{zproof}}[{name}\$domainCheck]
prove;
\end{{zproof}}

\begin[disabled]{{theorem}}{{rule {name}Def}}
  {name} = clos~{I}~{U}~{B}
\end{{theorem}}

\begin{{zproof}}
invoke {name};
prove;
\end{{zproof}}

\begin{{theorem}}{{{name}InPower}}
  {name} \in \power (\nat \fun \nat)
\end{{theorem}}

\begin{{zproof}}
use ClosInPow[I := {I}, U := {U}, B := {B}];
with enabled ({name}Def) prove;
\end{{zproof}}

\begin[disabled]{{theorem}}{{rule {name}UF}}
  \forall F: \power (\num \cross \num) | F \in {name} @ F \in \nat \fun \nat
\end{{theorem}}

\begin{{zproof}}
prove;
use ClosElemUF[I := {I}, U := {U}, B := {B}, F := F];
with enabled ({name}Def) prove;
\end{{zproof}}
"""]
    for k, f in enumerate(inits):
        out.append(rf"""\begin{{theorem}}{{rule {name}Init{k}}}
  {f} \in {name}
\end{{theorem}}

\begin{{zproof}}
with enabled ({name}Def) prove;
\end{{zproof}}
""")
    for k, u in enumerate(unops):
        out.append(rf"""\begin{{theorem}}{{rule {name}Unop{k}}}
  \forall F: \nat \fun \nat | F \in {name} @ {u}~F \in {name}
\end{{theorem}}

\begin{{zproof}}
with enabled ({name}Def) prove;
\end{{zproof}}
""")
    for k, b in enumerate(binops):
        out.append(rf"""\begin{{theorem}}{{rule {name}Binop{k}}}
  \forall F, G: \nat \fun \nat | F \in {name} \land G \in {name} @ {b}(F, G) \in {name}
\end{{theorem}}

\begin{{zproof}}
with enabled ({name}Def) prove;
\end{{zproof}}
""")
    return "\n".join(out)

def _split(var, items):
    if len(items) == 1:
        return "prove;"
    s = ""
    for it in items[:-1]:
        s += f"split {var} = {it};\ncases;\nprove;\nnext;\n"
    s += "prove;" + "\nnext;" * (len(items) - 1)
    return s

def closed(name, C, unops=None, binops=None):
    """Theorem NAME: closure C is closed under the given unary (or binary) operators."""
    if unops is not None:
        S = r'\{ ' + ', '.join(unops) + r' \}'
        return rf"""\begin{{theorem}}{{{name}}}
  {C} \in UClosed~{S}
\end{{theorem}}

\begin{{zproof}}
use {C}InPower;
with enabled (UClosedDef, {C}UF) prove;
{_split('u', unops)}
\end{{zproof}}
"""
    S = r'\{ ' + ', '.join(binops) + r' \}'
    return rf"""\begin{{theorem}}{{{name}}}
  {C} \in BClosed~{S}
\end{{theorem}}

\begin{{zproof}}
use {C}InPower;
with enabled (BClosedDef, {C}UF) prove;
{_split('b', binops)}
\end{{zproof}}
"""

def sub(name, A, inits, unops, binops, B):
    """Theorem NAME: A (= clos {inits} {unops} {binops}) is a subset of B, given the closedness
    lemmas BUClosedFor_NAME and BBClosedFor_NAME and the membership of the initial functions."""
    I = r'\{ ' + ', '.join(inits) + r' \}'
    U = r'\{ ' + ', '.join(unops) + r' \}'
    Bs = r'\{ ' + ', '.join(binops) + r' \}'
    return closed(name + 'U', B, unops=unops) + "\n" + closed(name + 'B', B, binops=binops) + rf"""
\begin{{theorem}}{{{name}}}
  {A} \subseteq {B}
\end{{theorem}}

\begin{{zproof}}
use ClosLeast[I := {I}, U := {U}, B := {Bs}, Z := {B}];
use {B}InPower;
use {name}U;
use {name}B;
with enabled ({A}Def) prove;
\end{{zproof}}
"""

def eqclos(name, A, B):
    """NAME: A = B from the two inclusions NAME1 (A in B) and NAME2 (B in A)."""
    return rf"""\begin{{theorem}}{{{name}}}
  {A} = {B}
\end{{theorem}}

\begin{{zproof}}
use {name}Sub1;
use {name}Sub2;
use {A}InPower;
use {B}InPower;
use SubAntisym[\nat \fun \nat][A := {A}, B := {B}];
prove;
\end{{zproof}}
"""
