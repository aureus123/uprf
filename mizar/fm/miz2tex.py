#!/usr/bin/env python3
"""Translate the definitions and theorems of ../text/uprf.miz into LaTeX in the
style of Formalized Mathematics (statements only, no proofs).

Usage: python3 miz2tex.py ../text/uprf.miz > body.tex
"""
import re
import sys

from extract import items

# ---------------------------------------------------------------- tokenizer

TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<sym>-'|c=|<=|>=|<>|->)
  | (?P<word>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<num>\d+)
  | (?P<one>[()\[\]{},.|&=<>+\-*/\\:;])
""", re.X)


def tokenize(s):
    toks = []
    pos = 0
    while pos < len(s):
        m = TOKEN_RE.match(s, pos)
        if not m:
            raise SyntaxError('cannot tokenize at: ' + s[pos:pos + 30])
        pos = m.end()
        if m.lastgroup != 'ws':
            toks.append(m.group(m.lastgroup))
    return toks


# ---------------------------------------------------------------- AST
# terms:    ('id', name) ('num', n) ('paren', t) ('bin', op, a, b)
#           ('app', fname, [args]) ('pre', fname, t) ('dot', f, x)
#           ('dot2', f, [args]) for f.(F,G), ('set', [elems])
# formulas: ('pred', op, [lhs], [rhs])  ('is', t, [attrs], neg)  ('istype', t, ty)
#           ('and', [f]) ('or', [f]) ('not', f) ('imp', a, b) ('iff', a, b)
#           ('for', segs, cond, body) ('ex', segs, cond) ('fparen', f)
# types:    ('type', [adjs], radix, [args])

# functors of the article with one argument and no parentheses (cst n, ...)
FUN_PREFIX = {'cst', 'funM', 'exprMinusI', 'exprIminusF', 'exprDminusF',
              'exprMinusIE', 'exprIminusE', 'exprMinusIK', 'exprW1', 'exprW2',
              'exprUK', 'exprP1K', 'exprCK', 'exprSK2'}
OP_PREFIX = {'opBoxA', 'opPlusIb'}
SET_PREFIX = {'Clos1', 'ClosB1', 'ClosGR', 'ClosGR0', 'ClosGRS', 'ClosVb'}
PREFIX = {'dom'} | FUN_PREFIX | OP_PREFIX | SET_PREFIX
# functors with a parenthesized argument list
FUN_FUNCS = {'exprOplus', 'exprOminus', 'exprOtimes', 'exprPlus', 'exprMinus'}
SET_FUNCS = {'clos', 'ClosBa', 'ClosGRb', 'ClosC', 'Funcs'}
FUNCS = FUN_FUNCS | SET_FUNCS | {'linv'}
ADJS = {'non', 'empty', 'finite'}
ATTRS = {'surj', 'rich', 'natural', 'empty', 'finite'}
RADIX_OF = {'Element', 'Subset', 'UnOp', 'BinOp'}
RADIX = {'Nat', 'object', 'set'} | RADIX_OF
TERM_STOP = {'st', 'holds', 'for', 'ex', 'implies', 'iff', 'or', '&', 'not',
             'is', 'in', 'c=', '=', '<>', '<', '<=', '>', '>=', 'misses',
             'meets', ')', ',', ']', '}', ':]', '\\]', 'being', 'if',
             'otherwise', 'where', ':', ';', 'means', 'equals', 'be', '*', '+',
             '-', "-'", '.', 'div', 'mod', '->'}
PREDS = {'=', '<>', '<', '<=', '>', '>=', 'in', 'c=', 'misses', 'meets'}


class Parser:
    def __init__(self, s):
        self.t = tokenize(s)
        self.i = 0

    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else None

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def expect(self, tok):
        if self.peek() != tok:
            raise SyntaxError('expected %r at %r' % (tok, self.t[self.i:self.i + 8]))
        self.i += 1

    def at_end(self):
        return self.i >= len(self.t)

    # ---------------- types
    def parse_type(self):
        adjs = []
        while self.peek() in ADJS:
            adjs.append(self.next())
        radix = self.next()
        args = []
        if radix in RADIX_OF and self.peek() == 'of':
            self.next()
            args.append(self.parse_term())
        return ('type', adjs, radix, args)

    # ---------------- variable segments: x,y being T, z st ...
    def parse_segs(self):
        segs = []
        while True:
            names = [self.next()]
            while self.peek() == ',' and self.peek(2) in (',', 'being', 'be',
                                                          'is', 'st', 'holds',
                                                          'for', 'ex', None):
                # a further name of the same segment
                self.next()
                names.append(self.next())
            typ = None
            if self.peek() in ('being', 'be', 'is'):
                self.next()
                typ = self.parse_type()
            segs.append((names, typ))
            if self.peek() == ',':
                self.next()
                continue
            return segs

    # ---------------- formulas
    def parse_formula(self):
        a = self.parse_or()
        if self.peek() == 'implies':
            self.next()
            return ('imp', a, self.parse_formula())
        if self.peek() == 'iff':
            self.next()
            return ('iff', a, self.parse_formula())
        return a

    def parse_or(self):
        fs = [self.parse_and()]
        while self.peek() == 'or':
            self.next()
            fs.append(self.parse_and())
        return fs[0] if len(fs) == 1 else ('or', fs)

    def parse_and(self):
        fs = [self.parse_neg()]
        while self.peek() == '&':
            self.next()
            fs.append(self.parse_neg())
        return fs[0] if len(fs) == 1 else ('and', fs)

    def parse_neg(self):
        tok = self.peek()
        if tok == 'not':
            self.next()
            return ('not', self.parse_neg())
        if tok == 'for':
            self.next()
            segs = self.parse_segs()
            cond = None
            if self.peek() == 'st':
                self.next()
                cond = self.parse_formula()
            if self.peek() == 'holds':
                self.next()
                body = self.parse_formula()
            else:  # for x ex y ..., for x for y ...
                body = self.parse_formula()
            return ('for', segs, cond, body)
        if tok == 'ex':
            self.next()
            segs = self.parse_segs()
            self.expect('st')
            return ('ex', segs, self.parse_formula())
        return self.parse_atom()

    def parse_atom(self):
        if self.peek() == '(':
            save = self.i
            try:
                return self.parse_pred_atom()
            except SyntaxError:
                self.i = save
            self.next()
            f = self.parse_formula()
            self.expect(')')
            return ('fparen', f)
        return self.parse_pred_atom()

    def parse_pred_atom(self):
        lhs = [self.parse_term()]
        while self.peek() == ',':
            self.next()
            lhs.append(self.parse_term())
        op = self.peek()
        if op in PREDS:
            self.next()
            return ('pred', op, lhs, [self.parse_term()])
        if op and op.startswith('is_'):
            self.next()
            rhs = [self.parse_term()]
            while self.peek() == ',':
                self.next()
                rhs.append(self.parse_term())
            return ('pred', op, lhs, rhs)
        if op == 'is' and self.peek(1) in RADIX:
            self.next()
            return ('istype', lhs[0], self.parse_type())
        if op == 'is':
            self.next()
            neg = False
            attrs = []
            while True:
                tok = self.peek()
                if tok == 'non':
                    self.next()
                    attrs.append(('non', self.next()))
                elif tok in ATTRS:
                    self.next()
                    attrs.append(('attr', tok))
                else:
                    break
            if not attrs:
                raise SyntaxError('no attribute at %r' % self.t[self.i:self.i + 5])
            return ('is', lhs[0], attrs, neg)
        raise SyntaxError('no predicate at %r' % self.t[self.i:self.i + 8])

    # ---------------- terms
    def parse_term(self):
        return self.parse_add()

    def parse_add(self):
        a = self.parse_mul()
        while self.peek() in ('+', '-', "-'"):
            op = self.next()
            a = ('bin', op, a, self.parse_mul())
        return a

    def parse_mul(self):
        a = self.parse_pow()
        while self.peek() in ('*', '/', 'div', 'mod'):
            op = self.next()
            a = ('bin', op, a, self.parse_pow())
        return a

    def parse_pow(self):
        return self.parse_prefix()

    def parse_prefix(self):
        tok = self.peek()
        if tok in PREFIX and self.peek(1) not in TERM_STOP | {None}:
            self.next()
            return ('pre', tok, self.parse_prefix())
        return self.parse_postfix()

    def parse_postfix(self):
        a = self.parse_primary()
        while True:
            tok = self.peek()
            if tok == '.':
                self.next()
                if self.peek() == '(':
                    self.next()
                    args = [self.parse_term()]
                    while self.peek() == ',':
                        self.next()
                        args.append(self.parse_term())
                    self.expect(')')
                    a = (('dot', a, ('paren', args[0])) if len(args) == 1
                         else ('dot2', a, args))
                else:
                    a = ('dot', a, self.parse_primary())
            else:
                return a

    def parse_primary(self):
        tok = self.next()
        if tok == '(':
            t = self.parse_term()
            self.expect(')')
            return ('paren', t)
        if tok == '{':
            elems = []
            if self.peek() != '}':
                elems.append(self.parse_term())
                while self.peek() == ',':
                    self.next()
                    elems.append(self.parse_term())
            self.expect('}')
            return ('set', elems)
        if tok in FUNCS and self.peek() == '(':
            self.next()
            args = [self.parse_term()]
            while self.peek() == ',':
                self.next()
                args.append(self.parse_term())
            self.expect(')')
            return ('app', tok, args)
        if re.fullmatch(r'\d+', tok):
            return ('num', tok)
        if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_#]*', tok) and tok not in TERM_STOP:
            return ('id', tok)
        raise SyntaxError('unexpected %r' % tok)


# ---------------------------------------------------------------- rendering

SPECIAL_IDS = {'NAT': r'\mathbb{N}', 'it': r'\mathit{it}', 'C6': r'\mathrm{C}_{6}',
               'C6K': r'\mathrm{C}_{6}^{\mathrm{K}}',
               'C6L': r'\mathrm{C}_{6}^{\mathrm{L}}'}

# the functions of the paper
FUN_NAMES = {
    'funI': 'I', 'funS': 'S', 'funD': 'D', 'funSq': 'Sq', 'funHf': 'Hf',
    'funRt': 'Rt', 'funE': 'E', 'funO': 'O', 'funSgn': 'Sgn', 'funQ': 'Q',
    'funMod3': 'Mod_3', 'funM3': 'M_3', 'funR': 'R', 'funA': 'A', 'funV': 'V',
    'funK': 'K', 'funL': 'L', 'funZ': 'Z', 'funY': 'Y', 'funG': 'G',
    'funH': 'H',
}
# unary operators, written as superscripts: F^+, F^box, ...
UNOP_SUP = {'opPlusI': '+', 'opBox': r'\square', 'opBox1': r'\square(1)',
            'opMinusI': '-', 'opInv': '-1'}
# binary operators, written infix
BINOP_SYM = {'opPlus': '+', 'opMinus': r'\mathbin{\dot{-}}', 'opComp': '',
             'opOplus': r'\oplus', 'opOminus': r'\ominus',
             'opOtimes': r'\otimes', 'opDiffE': r'\mathbin{\dot{-}_{E}}'}


def r_id(name):
    if name in SPECIAL_IDS:
        return SPECIAL_IDS[name]
    if name in FUN_NAMES:
        n = FUN_NAMES[name]
        return r'\mathrm{%s}' % n if '_' not in n else \
            r'\mathrm{%s}_{%s}' % tuple(n.split('_'))
    if name in UNOP_SUP:
        return r'{\cdot}^{%s}' % UNOP_SUP[name]
    if name in BINOP_SYM:
        return {'opComp': r'\circ', 'opPlus': '+'}.get(
            name, BINOP_SYM[name].replace(r'\mathbin', ''))
    m = re.fullmatch(r'([A-Za-z])(\d+)', name)
    if m:
        return '%s_{%s}' % (m.group(1), m.group(2))
    if len(name) == 1:
        return name
    return r'\mathrm{%s}' % name


def unparen(t):
    return t[1] if t[0] == 'paren' else t


# ---- kinds of terms: 'fun' (an element of Funcs(NAT,NAT)), 'op' (an
# operator), 'set' and 'num'

def type_kind(ty):
    if ty is None:
        return 'num'
    _, adjs, radix, args = ty
    if radix in ('UnOp', 'BinOp'):
        return 'op'
    if radix == 'Element' and args and args[0][0] == 'app' and \
            args[0][1] == 'Funcs':
        return 'fun'
    if radix in ('Subset', 'set'):
        return 'set'
    return 'num'


def kind(t):
    k = t[0]
    if k == 'paren':
        return kind(t[1])
    if k == 'id':
        n = t[1]
        if n in CTX.local:
            return CTX.local[n]
        if n in FUN_NAMES or n.startswith('expr'):
            return 'fun'
        if n in UNOP_SUP or n in BINOP_SYM:
            return 'op'
        if n in CTX.res:
            return type_kind(CTX.res[n])
        return 'set' if n.startswith('C') else 'num'
    if k == 'pre':
        if t[1] in FUN_PREFIX:
            return 'fun'
        if t[1] in OP_PREFIX:
            return 'op'
        return 'set'
    if k == 'app':
        if t[1] in FUN_FUNCS:
            return 'fun'
        if t[1] in SET_FUNCS:
            return 'set'
        return 'num'
    if k == 'dot':
        return 'fun' if kind(t[1]) == 'op' else 'num'
    if k == 'dot2':
        return 'fun'
    if k == 'bin' and t[1] == '*':
        return 'fun' if 'fun' in (kind(t[2]), kind(t[3])) else 'num'
    if k == 'set':
        return 'set'
    return 'num'


# composition: a thin space, where a line may break
COMP = r'\,\allowbreak '


def unop_sup(op):
    """the superscript of an operator term, or None"""
    op = unparen(op)
    if op[0] == 'id' and op[1] in UNOP_SUP:
        return UNOP_SUP[op[1]]
    if op[0] == 'pre' and op[1] == 'opBoxA':
        return r'\square(%s)' % rt(op[2])
    if op[0] == 'pre' and op[1] == 'opPlusIb':
        return '+%s' % rt(op[2])
    return None


def fun_atom(t, sup_base=False):
    """render a function term as an operand of an application or of a
    superscript: parentheses only when needed"""
    u = unparen(t)
    if u[0] in ('id', 'app', 'pre', 'num'):
        return rt(u)
    if u[0] == 'dot' and kind(u) == 'fun' and \
            (unop_sup(u[1]) is None or not sup_base):
        return rt(u)
    if u[0] == 'dot2' and not (unparen(u[1])[0] == 'id' and
                               unparen(u[1])[1] in BINOP_SYM):
        return rt(u)
    return '(%s)' % rt(u)


def comp_factors(t):
    """the factors of a composition F*G*H"""
    u = unparen(t)
    if u[0] == 'bin' and u[1] == '*' and kind(u) == 'fun':
        return comp_factors(u[2]) + comp_factors(u[3])
    return [t]


def comp_factor(t):
    u = unparen(t)
    if u[0] == 'dot' and unop_sup(u[1]) is not None:
        return rt(u)
    return fun_atom(t)


def atomic(t):
    return t[0] in ('id', 'num', 'paren', 'app', 'set', 'dot', 'dot2') or \
        (t[0] == 'pre' and t[1] != 'dom')


def rt(t):
    """render a term as LaTeX math"""
    k = t[0]
    if k == 'id':
        return r_id(t[1])
    if k == 'num':
        return t[1]
    if k == 'paren':
        if t[1][0] in ('id', 'num', 'app') or \
                (t[1][0] == 'dot' and kind(t[1]) == 'num'):
            return rt(t[1])
        return '(%s)' % rt(t[1])
    if k == 'bin':
        op, a, b = t[1], t[2], t[3]
        if op == '*' and kind(t) == 'fun':
            return COMP.join(comp_factor(x) for x in comp_factors(t))
        sym = {'+': '+', '-': '-', "-'": r'\mathbin{\dot{-}}', '*': r'\cdot ',
               'div': r'\mskip4mu\mathrm{div}\mskip4mu', 'mod': r'\bmod'}[op]
        return '%s %s %s' % (rt(a), sym, rt(b))
    if k == 'pre':
        f, a = t[1], t[2]
        if f == 'cst':
            return r'\overline{%s}' % rt(unparen(a))
        if f == 'funM':
            return r'\mathrm{M}_{%s}' % rt(unparen(a))
        if f in OP_PREFIX:
            return r'{\cdot}^{%s}' % unop_sup(t)
        if f == 'dom':
            return r'\mathrm{dom}\,%s' % rt(a)
        return r'\mathrm{%s}(%s)' % (f, rt(unparen(a)))
    if k == 'dot':
        f, x = t[1], t[2]
        sup = unop_sup(f)
        if sup is not None:
            return '%s^{%s}' % (fun_atom(x, sup_base=True), sup)
        if kind(f) == 'op':           # u.F, it.F
            return '%s(%s)' % (fun_atom(f), rt(unparen(x)))
        return '%s(%s)' % (fun_atom(f), rt(unparen(x)))
    if k == 'dot2':
        f, args = unparen(t[1]), t[2]
        if f[0] == 'id' and f[1] in BINOP_SYM:
            sym = BINOP_SYM[f[1]]
            if f[1] == 'opComp':
                return COMP.join(comp_factor(x) for x in args)
            return (' %s ' % sym).join(fun_atom(x) for x in args)
        return '%s(%s)' % (fun_atom(f), ', '.join(rt(unparen(x)) for x in args))
    if k == 'set':
        if not t[1]:
            return r'\emptyset'
        return r'\{%s\}' % ', '.join(rt(e) for e in t[1])
    if k == 'app':
        f, args = t[1], [rt(unparen(a)) for a in t[2]]
        if f == 'Funcs':
            return r'\mathbb{N}^{\mathbb{N}}'
        return r'\mathrm{%s}(%s)' % (f, r',\allowbreak '.join(args))
    raise ValueError(t)


def m(s):
    return '$%s$' % s


# ---- types

def article(phrase):
    p = phrase.lstrip('\\{$').lower()
    vowel = p[:1] in 'aeiou' and not p.startswith(('unary', 'one'))
    return ('an ' if vowel else 'a ') + phrase


def rtype2(ty, plural=False):
    """(head, tail): the variables go between them, as in 'element v of G'"""
    _, adjs, radix, args = ty
    pl = plural
    a = ['non empty' if x == 'non' else x for x in adjs]
    a = ' '.join(a).replace('non empty empty', 'non empty')
    nouns = {
        'Nat': ('natural number', 'natural numbers'),
        'object': ('object', 'objects'),
        'set': ('set', 'sets'),
    }
    tail = ''
    if radix in nouns:
        noun = nouns[radix][1 if pl else 0]
    elif type_kind(ty) == 'fun':
        noun = 'functions' if pl else 'function'
        tail = r' from $\mathbb{N}$ into $\mathbb{N}$'
    elif radix == 'Element' and args == [('id', 'NAT')]:
        noun = nouns['Nat'][1 if pl else 0]
    elif radix == 'Element':
        noun = 'elements' if pl else 'element'
        tail = ' of ' + m(rt(args[0]))
    elif radix == 'Subset':
        noun = 'subsets' if pl else 'subset'
        tail = ' of ' + m(rt(args[0]))
    elif radix == 'UnOp':
        noun = 'unary operations' if pl else 'unary operation'
        tail = ' on ' + m(rt(args[0]))
    elif radix == 'BinOp':
        noun = 'binary operations' if pl else 'binary operation'
        tail = ' on ' + m(rt(args[0]))
    else:
        noun = radix
    return (a + ' ' + noun).strip(), tail


def rtype(ty, plural=False):
    h, t = rtype2(ty, plural)
    return h + t


def typed_vars(names, ty, art=False):
    """'element $v$ of $G$', 'natural numbers $i$, $j$'"""
    vs = ', '.join(m(r_id(n)) for n in names)
    if ty is None:
        return vs
    h, t = rtype2(ty, len(names) > 1)
    if art and len(names) == 1:
        h = article(h)
    return '%s %s%s' % (h, vs, t)


class Ctx:
    """reserved variables"""
    def __init__(self):
        self.res = {}
        self.local = {}       # kinds of the variables bound in the item
        self.iff = 'iff'      # 'if and only if' in theorems, as in FM


CTX = Ctx()


def seg_phrase(segs, quant):
    """'every natural number $i$ and every $f$', 'a natural number $k$ and $f$'"""
    parts = []
    for names, ty in segs:
        if quant == 'every':
            parts.append(('every ' if ty is not None else '') +
                         typed_vars(names, ty))
        else:
            parts.append(typed_vars(names, ty, art=True))
    return ' and '.join(parts)


def rf(f, top=False):
    """render a formula as text with inline math"""
    k = f[0]
    if k == 'fparen':
        return '(%s)' % rf(f[1])
    if k == 'and':
        return ' and '.join(rf(x) for x in f[1])
    if k == 'or':
        return ' or '.join(rf(x) for x in f[1])
    if k == 'imp':
        return 'if %s, then %s' % (rf(f[1]), rf(f[2]))
    if k == 'iff':
        return '%s %s %s' % (rf(f[1]), CTX.iff, rf(f[2]))
    if k == 'not':
        return rneg(f[1])
    if k == 'for':
        s = 'for ' + seg_phrase(f[1], 'every')
        if f[1][0][1] is None:
            s = 'for every ' + seg_phrase(f[1], 'every')
        if f[2] is not None:
            s += ' such that ' + rf(f[2])
        return s + ' holds ' + rf(f[3])
    if k == 'ex':
        names = sum(len(n) for n, _ in f[1])
        verb = 'there exist ' if names > 1 else 'there exists '
        ph = seg_phrase(f[1], 'ex')
        return verb + ph + ' such that ' + rf(f[2])
    if k == 'pred':
        return rpred(f)
    if k == 'is':
        return ris(f, False)
    if k == 'istype':
        return '%s is %s' % (m(rt(f[1])), article(rtype(f[2])))
    raise ValueError(f)


def ris(f, neg):
    t, attrs = f[1], f[2]
    words = []
    for a in attrs:
        if a[0] == 'non':
            words.append('non ' + a[1])
        else:
            words.append(a[1])
    if len(words) > 1:
        ws = ', '.join(words[:-1]) + ' and ' + words[-1]
    else:
        ws = words[0]
    return '%s is %s%s' % (m(rt(t)), 'not ' if neg else '', ws)


PRED_TEXT = {
    'is_closed_under': ('is closed under', None),
}


def rpred(f, neg=False):
    op, lhs, rhs = f[1], f[2], f[3]
    L = [rt(x) for x in lhs]
    R = [rt(x) for x in rhs]
    if op in ('=', '<>', '<', '<=', '>', '>=', 'in', 'c='):
        sym = {'=': '=', '<>': r'\neq', '<': '<', '<=': r'\leq', '>': '>',
               '>=': r'\geq', 'in': r'\in', 'c=': r'\subseteq'}[op]
        if neg:
            sym = {'=': r'\neq', r'\neq': '=', '<': r'\geq', r'\leq': '>',
                   '>': r'\leq', r'\geq': '<', r'\in': r'\notin',
                   r'\subseteq': r'\not\subseteq'}[sym]
        return m('%s %s %s' % (L[0], sym, R[0]))
    if op in ('misses', 'meets'):
        if neg:
            op = {'misses': 'meets', 'meets': 'misses'}[op]
        return '%s %s %s' % (m(L[0]), op, m(R[0]))
    words, conj = PRED_TEXT[op]
    if neg:
        words = words.replace('is ', 'is not ', 1)
    if conj:
        rr = (' %s ' % conj).join(m(x) for x in R)
    else:
        rr = ', '.join(m(x) for x in R)
    return '%s %s %s' % (m(L[0]), words, rr)


def rneg(f):
    k = f[0]
    if k == 'fparen' and f[1][0] == 'ex':
        f = f[1]
        k = 'ex'
    if k == 'ex':
        return 'there exists no %s such that %s' % (
            ' and no '.join(typed_vars(n, ty) for n, ty in f[1]), rf(f[2]))
    if k == 'pred':
        return rpred(f, neg=True)
    if k == 'is':
        return ris(f, True)
    if k == 'fparen':
        return 'not ' + rf(f)
    return 'not ' + rf(f)


def render_theorem(f):
    """'Let us consider ... Suppose ... Then ...' style"""
    segs = []
    conds = []
    body = f
    while body[0] == 'for' and (body[2] is not None or body[3][0] in ('for', 'imp')
                                or True):
        segs.extend(body[1])
        if body[2] is not None:
            conds.append(body[2])
        body = body[3]
        if body[0] != 'for':
            break
    if segs and body[0] == 'imp':
        conds.append(body[1])
        body = body[2]
    out = ''
    if segs:
        parts = []
        for names, ty in segs:
            parts.append(typed_vars(names, ty, art=True))
        if len(parts) > 1:
            out += 'Let us consider %s, and %s. ' % (', '.join(parts[:-1]), parts[-1])
        else:
            out += 'Let us consider %s. ' % parts[0]
        if conds:
            out += 'Suppose %s. ' % ' and '.join(rf(c) for c in conds)
        out += 'Then ' + render_concl(body) + '.'
        return out
    if body[0] == 'imp':
        return 'If %s, then %s.' % (rf(body[1]), render_concl(body[2]))
    s = render_concl(body)
    if s.startswith('('):
        return '(' + s[1].upper() + s[2:] + '.'
    if s.startswith('$') or s.startswith('\\'):
        return s + '.'
    return s[0].upper() + s[1:] + '.'


def render_concl(f):
    if f[0] == 'and' and (len(f[1]) >= 3 or any(
            x[0] in ('fparen', 'for', 'ex', 'imp') for x in f[1])):
        items = [rf(x[1] if x[0] == 'fparen' else x) for x in f[1]]
        return r'\begin{fmlist}' + ', and'.join(r'\item %s' % x for x in items) + \
            r'\fmlistend'
    return rf(f)


# ---------------------------------------------------------------- definitions

def let_phrase(lets):
    """'Let F be a function from N into N, and x be a natural number.'"""
    parts = []
    for names, ty in lets:
        if ty is None:
            ty = None
            # reserved: find the type
            for n in names:
                rty = CTX.res.get(n)
                parts.append((n, rty))
        else:
            for n in names:
                parts.append((n, ty))
    # group consecutive names with the same type text
    groups = []
    for n, ty in parts:
        txt = rtype(ty) if ty else None
        if groups and groups[-1][1] == txt:
            groups[-1][0].append(n)
        else:
            groups.append(([n], txt))
    phr = []
    for ns, txt in groups:
        vs = ', '.join(m(r_id(n)) for n in ns)
        if txt is None:
            phr.append(vs)
        elif len(ns) > 1:
            tp = rtype(next(ty for n, ty in parts if n == ns[0]), True)
            phr.append('%s be %s' % (vs, tp))
        else:
            phr.append('%s be %s' % (vs, article(txt)))
    if len(phr) == 1:
        return 'Let %s.' % phr[0]
    return 'Let %s, and %s.' % (', '.join(phr[:-1]), phr[-1])


DEFNO = [0]


def defno():
    DEFNO[0] += 1
    return DEFNO[0]


def render_head(kind, head):
    """the defined notion, rendered"""
    if kind in ('pred', 'attr'):
        f = Parser(head).parse_pred_atom()
        return rf(f) if f[0] == 'pred' else ris(f, False)
    return m(rt(Parser(head).parse_term()))


def parse_cases(text):
    """'A if C1, B if C2 otherwise D' -> [(A,C1),(B,C2)], D"""
    cases = []
    p = Parser(text)
    while True:
        t = p.parse_term()
        if p.peek() == 'if':
            p.next()
            c = p.parse_formula()
            cases.append((t, c))
            if p.peek() == ',':
                p.next()
                continue
            p.expect('otherwise')
            return cases, p.parse_term()
        return None, t


def collect_kinds(f):
    """record in CTX.local the kinds of the variables bound in f"""
    if isinstance(f, tuple):
        if f and f[0] in ('for', 'ex'):
            for names, ty in f[1]:
                for n in names:
                    CTX.local[n] = type_kind(ty if ty is not None
                                             else CTX.res.get(n))
        for x in f:
            collect_kinds(x)
    elif isinstance(f, list):
        for x in f:
            collect_kinds(x)


def set_local(lets):
    CTX.local = {}
    for names, ty in lets:
        for n in names:
            CTX.local[n] = type_kind(ty if ty is not None else CTX.res.get(n))


def def_body(f):
    """the body of a definition; long conjunctions as a list"""
    if f[0] == 'and' and len(f[1]) >= 3:
        return r'\fmsameline' + render_concl(f)
    return rf(f)


def render_definition(lines):
    out = []
    text = ' '.join(lines)
    text = re.sub(r':\w+:', ' ', text)
    # split into statements at ';' (correctness conditions dropped)
    stmts = [s.strip() for s in text.split(';') if s.strip()]
    lets = []
    assume = None
    i = 0
    while i < len(stmts):
        s = stmts[i]
        if s.startswith('let '):
            p = Parser(s[4:])
            lets.extend(p.parse_segs())
        elif s.startswith('assume '):
            assume = re.sub(r'^assume\s+\w+:\s*', '', s)
        elif s.startswith('redefine func '):
            head, ytype = re.match(r'redefine func (.*?)\s*->\s*(.*)$', s).groups()
            set_local(lets)
            out.append('%s One can check that %s is %s.' % (
                let_phrase(lets), m(rt(Parser(head).parse_term())),
                article(rtype(Parser(ytype).parse_type()))))
        elif re.match(r'(pred|attr|func) ', s):
            mm = re.match(r'(pred|attr|func) (.*?)\s+(means|equals)\s+(.*)$', s,
                          re.S)
            kind, head, how, body = mm.groups()
            body = re.sub(r'\s+(coherence|consistency|existence|uniqueness|'
                          r'symmetry|irreflexivity)\b.*$', '', body)
            props = re.findall(r'\b(symmetry|irreflexivity)\b', s)
            ytype = None
            if kind == 'func':
                head, ytype = re.match(r'(.*?)\s*->\s*(.*)$', head).groups()
            set_local(lets)
            if ytype:
                CTX.local['it'] = type_kind(Parser(ytype).parse_type())
            intro = (let_phrase(lets) + ' ') if lets else ''
            if assume:
                intro += 'Assume that %s. ' % rf(Parser(assume).parse_formula())
            n = defno()
            if kind in ('pred', 'attr'):
                hd = render_head(kind, head)
                f = Parser(body).parse_formula()
                collect_kinds(f)
                out.append(intro + r'We say that %s if and only if' % hd)
                out.append(r'\fmdef{%d}{%s.}' % (n, def_body(f)))
                for pr in props:
                    out.append('Note that the predicate is %s.' % {
                        'symmetry': 'symmetric',
                        'irreflexivity': 'irreflexive'}[pr])
            else:
                hd = render_head(kind, head)
                yt = rtype(Parser(ytype).parse_type())
                if how == 'means':
                    p = Parser(body)
                    f = p.parse_formula()
                    collect_kinds(f)
                    out.append(intro + 'The functor %s yielding %s is defined by'
                               % (hd, article(yt)))
                    if p.peek() == 'if':      # means ... if ... otherwise ...
                        p.next()
                        c = p.parse_formula()
                        p.expect('otherwise')
                        g = p.parse_formula()
                        collect_kinds(g)
                        out.append(r'\fmdef{%d}{%s, if %s, and %s, otherwise.}'
                                   % (n, rf(f), rf(c), rf(g)))
                    else:
                        out.append(r'\fmdef{%d}{%s.}' % (n, def_body(f)))
                else:
                    cases, other = parse_cases(body)
                    if cases is None:
                        out.append(intro + 'The functor %s yielding %s is defined '
                                   'by the term' % (hd, article(yt)))
                        out.append(r'\fmdef{%d}{%s.}' % (n, m(rt(other))))
                    else:
                        out.append(intro + 'The functor %s yielding %s is defined '
                                   'by the term' % (hd, article(yt)))
                        conds = ['if %s,' % rf(c) for t, c in cases]
                        conds.append('otherwise.')
                        wide = max(map(len, conds)) > 70
                        rows = [r'%s, & %s' % (rt(t), c if wide else r'\text{%s}' % c)
                                for t, c in zip([t for t, _ in cases] + [other], conds)]
                        out.append(r'\fmdef{%d}{$\left\{\begin{array}'
                                   r'{@{\,}l@{\quad}%s@{}}%s\end{array}\right.$}'
                                   % (n, r'p{0.55\linewidth}' if wide else 'l',
                                      r'\\'.join(rows)))
        i += 1
    return '\n\n'.join(out)


def render_registration(lines):
    text = ' '.join(lines)
    lets = []
    for s in [x.strip() for x in text.split(';') if x.strip()]:
        if s.startswith('let '):
            lets.extend(Parser(s[4:]).parse_segs())
        elif s.startswith('cluster '):
            set_local(lets)
            mm = re.match(r'cluster (.*?) -> (.*)$', s)
            t = Parser(mm.group(1)).parse_term()
            return '%s One can check that %s is %s.' % (let_phrase(lets), m(rt(t)),
                                               mm.group(2))
    return ''


def render_reserve(text):
    """'I for set' / 'f,g for Function of I,NAT' -> From now on ..."""
    parts = []
    segre = re.compile(r'((?:[A-Za-z0-9_]+\s*,\s*)*[A-Za-z0-9_]+)\s+for\s+'
                       r'(.*?)(?=,\s*(?:[A-Za-z0-9_]+\s*,\s*)*[A-Za-z0-9_]+'
                       r'\s+for\s|$)')
    for names, ty in segre.findall(text):
        names = [x.strip() for x in names.split(',')]
        tyast = Parser(ty).parse_type()
        for n in names:
            CTX.res[n] = tyast
        vs = ', '.join(m(r_id(n)) for n in names)
        if len(names) > 1:
            parts.append('%s denote %s' % (vs, rtype(tyast, True)))
        else:
            parts.append('%s denotes %s' % (vs, article(rtype(tyast))))
    return 'From now on %s.' % ', '.join(parts)


SCHEMES = {
    'UFunEx': r"""The scheme \emph{UFunEx} deals with a unary functor
$\mathcal{T}$ yielding a natural number, and states that there exists a
function $f$ from $\mathbb{N}$ into $\mathbb{N}$ such that for every natural
number $x$, $f(x) = \mathcal{T}(x)$.""",
    'UFunUq': r"""The scheme \emph{UFunUq} deals with a unary functor
$\mathcal{T}$ yielding a natural number and functions $\mathcal{F}$,
$\mathcal{G}$ from $\mathbb{N}$ into $\mathbb{N}$, and states that
$\mathcal{F} = \mathcal{G}$ provided for every natural number $x$,
$\mathcal{F}(x) = \mathcal{T}(x)$, and for every natural number $x$,
$\mathcal{G}(x) = \mathcal{T}(x)$.""",
    'UOpEx': r"""The scheme \emph{UOpEx} deals with a binary functor
$\mathcal{T}$ from the functions from $\mathbb{N}$ into $\mathbb{N}$ and the
natural numbers into the natural numbers, and states that there exists a
unary operation $u$ on $\mathbb{N}^{\mathbb{N}}$ such that for every function
$F$ from $\mathbb{N}$ into $\mathbb{N}$ and every natural number $x$,
$u(F)(x) = \mathcal{T}(F, x)$.""",
    'UOpUq': r"""The scheme \emph{UOpUq} deals with a binary functor
$\mathcal{T}$ as in \emph{UOpEx} and unary operations $\mathcal{U}$,
$\mathcal{V}$ on $\mathbb{N}^{\mathbb{N}}$, and states that
$\mathcal{U} = \mathcal{V}$ provided for every function $F$ from $\mathbb{N}$
into $\mathbb{N}$ and every natural number $x$,
$\mathcal{U}(F)(x) = \mathcal{T}(F, x)$ and
$\mathcal{V}(F)(x) = \mathcal{T}(F, x)$.""",
    'BOpEx': r"""The scheme \emph{BOpEx} deals with a ternary functor
$\mathcal{T}$ from two functions from $\mathbb{N}$ into $\mathbb{N}$ and a
natural number into the natural numbers, and states that there exists a
binary operation $b$ on $\mathbb{N}^{\mathbb{N}}$ such that for all functions
$F$, $G$ from $\mathbb{N}$ into $\mathbb{N}$ and every natural number $x$,
$b(F, G)(x) = \mathcal{T}(F, G, x)$.""",
    'BOpUq': r"""The scheme \emph{BOpUq} deals with a ternary functor
$\mathcal{T}$ as in \emph{BOpEx} and binary operations $\mathcal{B}$,
$\mathcal{C}$ on $\mathbb{N}^{\mathbb{N}}$, and states that
$\mathcal{B} = \mathcal{C}$ provided for all functions $F$, $G$ from
$\mathbb{N}$ into $\mathbb{N}$ and every natural number $x$,
$\mathcal{B}(F, G)(x) = \mathcal{T}(F, G, x)$ and
$\mathcal{C}(F, G)(x) = \mathcal{T}(F, G, x)$.""",
}

# (prefix of a comment of the article, title of the section that it starts)
SECTIONS = [
    ('Section 2 of D. E. Severin', 'Preliminaries'),
    ('Basic functions', 'Basic and Arithmetic Functions'),
    ('Operators', 'Operators'),
    ('Bases and closures', 'Bases and Closures'),
    ('Arithmetic facts about Rt and E', r'Arithmetic Facts about $\mathrm{Rt}$ and $\mathrm{E}$'),
    ('Section 6: iteration', r'The Basis $\langle \overline{1}, \mathrm{E}, F^{+}, FG, F^{\square}\rangle$'),
    ('Definition 6.1', 'Definition 6.1 and Lemmas 6.2--6.6'),
    ('Theorem 6.7 (closure part)', 'Theorem 6.7'),
    ('Cantor pairing functions', 'Cantor Pairing Functions'),
    ('Bases <1, G, F^+, FG, F^box> for a single', 'Theorem 6.8'),
    ('Remark 6.9', r'Remark 6.9: Iteration Started at $1$'),
    ('Questions left open in the paper', r'Iteration Started at Any $a \geq 1$'),
    ('The shifted operator F^+b(x)', 'A Shifted Unary Operator'),
    ('Open problem 3.2 of the README', 'Inversion and General Recursive Functions'),
    ('The constant 1 cannot be dropped', r'The Constant $\overline{1}$ and the Successor'),
    ('The shifted operator with inversion', 'The Shifted Operator with Inversion'),
    ('Any constant n >= 1', r'Any Constant $\overline{n}$, $n \geq 1$'),
]


def plural(n, word):
    return word if n == 1 else word + 's'


def consequence(refs, numbers):
    """'The theorem is a consequence of (3) and (7).'"""
    ns = []
    for r in refs:
        if r in numbers and numbers[r] not in ns:
            ns.append(numbers[r])
    if not ns:
        return ''
    xs = ['(%d)' % n for n in ns]
    if len(xs) == 1:
        lst = xs[0]
    elif len(xs) == 2:
        lst = '%s and %s' % tuple(xs)
    else:
        lst = ', '.join(xs[:-1]) + ', and ' + xs[-1]
    return 'The theorem is a consequence of %s.' % lst


def main(path):
    out = []      # (kind, text)
    thno = 0
    numbers = {}  # theorem label -> number
    for it in items(path):
        k = it['kind']
        if k == 'comment':
            for key, title in SECTIONS:
                if it['text'].startswith(key):
                    out.append(('section', r'\fmsection{%s}' % title))
            continue
        if k == 'reserve':
            out.append(('para', render_reserve(it['text'])))
        elif k == 'definition':
            try:
                out.append(('para', render_definition(it['lines'])))
            except (SyntaxError, IndexError, KeyError, ValueError,
                    AttributeError) as e:
                sys.stderr.write('DEFINITION: %s\n  %s\n' % (e, it['lines']))
        elif k == 'registration':
            out.append(('para', render_registration(it['lines'])))
        elif k == 'scheme':
            name = re.match(r'scheme (\w+)', it['text']).group(1)
            out.append(('para', SCHEMES[name]))
        elif k == 'theorem':
            thno += 1
            CTX.iff = 'if and only if'
            try:
                f = Parser(it['text']).parse_formula()
                CTX.local = {}
                collect_kinds(f)
                body = render_theorem(f)
            except (SyntaxError, IndexError, KeyError, ValueError) as e:
                sys.stderr.write('THEOREM %s: %s\n  %s\n' % (it['label'], e,
                                                            it['text']))
                body = r'\texttt{%s}' % it['text']
            CTX.iff = 'iff'
            if body.startswith(r'\begin{fmlist}'):
                body = r'\fmsameline' + body
            c = consequence(it['refs'], numbers)
            if c and body.endswith(r'\fmlistend.'):
                body += r'\fmafterlist{%s}' % c
            elif c:
                body += ' ' + c
            numbers[it['label']] = thno
            out.append(('thm', r'\fmthm{%d}{%s}{%s}' % (thno, body, it['label'])))
    # "Now we state the proposition(s):" before each run of theorems, appended
    # to the preceding paragraph when there is one
    res = []
    i = 0
    while i < len(out):
        k, t = out[i]
        if k == 'thm':
            j = i
            while j < len(out) and out[j][0] == 'thm':
                j += 1
            now = 'Now we state the %s:' % plural(j - i, 'proposition')
            if res and res[-1][0] == 'para':
                res[-1] = ('para', res[-1][1] + ' ' + now)
            else:
                res.append(('para', now))
            res.extend(out[i:j])
            i = j
            continue
        res.append((k, t))
        i += 1
    print('\n\n'.join(r'\fmpara{%s}' % t if k == 'para' else t for k, t in res))


if __name__ == '__main__':
    main(sys.argv[1])
