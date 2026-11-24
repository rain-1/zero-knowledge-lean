package kernel

import (
	"fmt"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// ---------------------------------------------------------------------------
// Surface syntax (a small Lean 4 subset)
//
//   def      name (x y : A) ... : T := e
//   theorem  name (x y : A) ... : T := e        -- `lemma` is a synonym
//   theorem  name ... : T := sorry               -- public statement, no proof
//
//   e ::= fun (x : A) (y z : B) => e   |  λ ...      (binder types required)
//       | ∀ (x : A) (y : B), e         |  ∀ x y : A, e  | forall | Π
//       | e → e  |  e -> e
//       | e e                          (application)
//       | x | Prop | Type | Type n | Sort n | ( e )
//
// Comments: `-- ...` and `/- ... -/`. Definitions are *transparent macros*:
// every reference is replaced by the elaborated body, so the kernel term is
// definition-free and the type checker sees ordinary β-redexes.
// ---------------------------------------------------------------------------

type tok struct {
	kind string // "id", "num", "sym", "eof"
	s    string
	pos  int
}

func isIdStart(r rune) bool {
	return r == '_' || unicode.IsLetter(r) && r != 'λ' && r != 'Π'
}
func isIdRest(r rune) bool {
	return isIdStart(r) || unicode.IsDigit(r) || r == '\'' || r == '.' || r == '!' || r == '?' ||
		(r >= '₀' && r <= '₉')
}

func lex(src string) ([]tok, error) {
	var out []tok
	i := 0
	for i < len(src) {
		r, w := utf8.DecodeRuneInString(src[i:])
		switch {
		case unicode.IsSpace(r):
			i += w
		case strings.HasPrefix(src[i:], "--"):
			for i < len(src) && src[i] != '\n' {
				i++
			}
		case strings.HasPrefix(src[i:], "/-"):
			depth := 0
			for i < len(src) {
				if strings.HasPrefix(src[i:], "/-") {
					depth++
					i += 2
				} else if strings.HasPrefix(src[i:], "-/") {
					depth--
					i += 2
					if depth == 0 {
						break
					}
				} else {
					i++
				}
			}
		case unicode.IsDigit(r):
			j := i
			for j < len(src) && src[j] >= '0' && src[j] <= '9' {
				j++
			}
			out = append(out, tok{"num", src[i:j], i})
			i = j
		case isIdStart(r):
			j := i + w
			for j < len(src) {
				r2, w2 := utf8.DecodeRuneInString(src[j:])
				if !isIdRest(r2) {
					break
				}
				j += w2
			}
			out = append(out, tok{"id", src[i:j], i})
			i = j
		default:
			matched := false
			for _, sym := range []string{":=", "=>", "->", "→", "∀", "λ", "Π", "(", ")", ":", ",", "↦"} {
				if strings.HasPrefix(src[i:], sym) {
					out = append(out, tok{"sym", sym, i})
					i += len(sym)
					matched = true
					break
				}
			}
			if !matched {
				return nil, fmt.Errorf("unexpected character %q at offset %d", r, i)
			}
		}
	}
	out = append(out, tok{"eof", "", len(src)})
	return out, nil
}

// Decl is an elaborated top-level declaration.
type Decl struct {
	Kind      string // "def" or "theorem"
	Name      string
	Type      int // closed kernel term
	Value     int // closed kernel term, -1 if `sorry`
	BodyStart int // source span of the body expression (for statement stripping)
	BodyEnd   int
	Signature string // source text of binders and type, e.g. `(A : Prop) : A → A`
}

// Env is the result of elaborating a file.
type Env struct {
	S     *Store
	Decls []*Decl
	byNm  map[string]*Decl
	Src   string
}

func (e *Env) Lookup(name string) (*Decl, bool) { d, ok := e.byNm[name]; return d, ok }

type parser struct {
	toks []tok
	p    int
	env  *Env
	src  string
}

func (ps *parser) peek() tok { return ps.toks[ps.p] }
func (ps *parser) next() tok { t := ps.toks[ps.p]; ps.p++; return t }
func (ps *parser) is(s string) bool {
	t := ps.peek()
	return (t.kind == "sym" || t.kind == "id") && t.s == s
}
func (ps *parser) errf(format string, a ...any) error {
	t := ps.peek()
	line := 1 + strings.Count(ps.src[:t.pos], "\n")
	return fmt.Errorf("line %d: %s", line, fmt.Sprintf(format, a...))
}
func (ps *parser) expect(s string) error {
	if !ps.is(s) {
		return ps.errf("expected %q, got %q", s, ps.peek().s)
	}
	ps.p++
	return nil
}

var keywords = map[string]bool{
	"def": true, "theorem": true, "lemma": true, "fun": true, "forall": true,
	"Prop": true, "Type": true, "Sort": true, "sorry": true,
}

// Parse elaborates a whole source file.
func Parse(src string) (*Env, error) {
	toks, err := lex(src)
	if err != nil {
		return nil, err
	}
	env := &Env{S: NewStore(), byNm: map[string]*Decl{}, Src: src}
	ps := &parser{toks: toks, env: env, src: src}
	for ps.peek().kind != "eof" {
		if err := ps.decl(); err != nil {
			return nil, err
		}
	}
	return env, nil
}

type binder struct {
	name string
	ty   int
}

// binders parses `(x y : A) (z : B) ...` or the bare form `x y : A`.
func (ps *parser) binders(locals []string, allowBare bool) ([]binder, error) {
	var bs []binder
	cur := append([]string{}, locals...)
	group := func(closing bool) error {
		var names []string
		for ps.peek().kind == "id" && !keywords[ps.peek().s] {
			names = append(names, ps.next().s)
		}
		if len(names) == 0 {
			return ps.errf("expected binder name")
		}
		if err := ps.expect(":"); err != nil {
			return err
		}
		ty, err := ps.expr(cur)
		if err != nil {
			return err
		}
		if closing {
			if err := ps.expect(")"); err != nil {
				return err
			}
		}
		// each name's type is elaborated in the scope *before* that name
		for i, n := range names {
			t := ty
			if i > 0 {
				// re-parse not possible; instead lift: names in one group share a type
				// that cannot mention earlier names of the same group. Because the
				// type is closed w.r.t. the group, we must shift its loose bvars by i.
				t = ps.shift(ty, i, 0)
			}
			bs = append(bs, binder{n, t})
			cur = append(cur, n)
		}
		return nil
	}
	if ps.is("(") {
		for ps.is("(") {
			ps.next()
			if err := group(true); err != nil {
				return nil, err
			}
		}
		return bs, nil
	}
	if allowBare {
		if err := group(false); err != nil {
			return nil, err
		}
		return bs, nil
	}
	return nil, ps.errf("expected binder group")
}

// shift lifts loose bound variables >= cutoff by d (used only by the elaborator).
func (ps *parser) shift(t, d, cutoff int) int {
	s := ps.env.S
	n := s.N(t)
	if n.G <= cutoff {
		return t
	}
	switch n.Tag {
	case TBVar:
		if n.A >= cutoff {
			return s.BVar(n.A + d)
		}
		return t
	case TPi, TLam:
		return s.Mk(n.Tag, ps.shift(n.A, d, cutoff), ps.shift(n.B, d, cutoff+1))
	case TApp:
		return s.Mk(n.Tag, ps.shift(n.A, d, cutoff), ps.shift(n.B, d, cutoff))
	}
	return t
}

func (ps *parser) wrap(tag int, bs []binder, body int) int {
	for i := len(bs) - 1; i >= 0; i-- {
		body = ps.env.S.Mk(tag, bs[i].ty, body)
	}
	return body
}

func (ps *parser) decl() error {
	t := ps.next()
	kind := t.s
	switch kind {
	case "def", "theorem", "lemma":
	default:
		ps.p--
		return ps.errf("expected `def` or `theorem`, got %q", t.s)
	}
	if kind == "lemma" {
		kind = "theorem"
	}
	nt := ps.next()
	if nt.kind != "id" || keywords[nt.s] {
		return ps.errf("expected a name")
	}
	if _, dup := ps.env.byNm[nt.s]; dup {
		return ps.errf("duplicate declaration %s", nt.s)
	}
	sigStart := ps.peek().pos
	var bs []binder
	var err error
	if ps.is("(") {
		if bs, err = ps.binders(nil, false); err != nil {
			return err
		}
	}
	names := make([]string, len(bs))
	for i, b := range bs {
		names[i] = b.name
	}
	if err := ps.expect(":"); err != nil {
		return err
	}
	ty, err := ps.expr(names)
	if err != nil {
		return err
	}
	sigEnd := ps.peek().pos
	if err := ps.expect(":="); err != nil {
		return err
	}
	sig := strings.Join(strings.Fields(ps.src[sigStart:sigEnd]), " ")
	d := &Decl{Kind: kind, Name: nt.s, Type: ps.wrap(TPi, bs, ty), Value: -1, Signature: sig}
	d.BodyStart = ps.peek().pos
	if ps.is("sorry") {
		ps.next()
		if kind == "def" {
			return ps.errf("definitions must have a body")
		}
	} else {
		body, err := ps.expr(names)
		if err != nil {
			return err
		}
		d.Value = ps.wrap(TLam, bs, body)
	}
	lastTok := ps.toks[ps.p-1]
	d.BodyEnd = lastTok.pos + len(lastTok.s)
	ps.env.Decls = append(ps.env.Decls, d)
	ps.env.byNm[d.Name] = d
	return nil
}

// expr := binder-form | arrow
func (ps *parser) expr(locals []string) (int, error) {
	s := ps.env.S
	switch {
	case ps.is("fun") || ps.is("λ"):
		ps.next()
		bs, err := ps.binders(locals, true)
		if err != nil {
			return 0, err
		}
		if !(ps.is("=>") || ps.is("↦")) {
			return 0, ps.errf("expected =>")
		}
		ps.next()
		inner := locals
		for _, b := range bs {
			inner = append(append([]string{}, inner...), b.name)
		}
		body, err := ps.expr(inner)
		if err != nil {
			return 0, err
		}
		return ps.wrap(TLam, bs, body), nil
	case ps.is("∀") || ps.is("forall") || ps.is("Π"):
		ps.next()
		bs, err := ps.binders(locals, true)
		if err != nil {
			return 0, err
		}
		if err := ps.expect(","); err != nil {
			return 0, err
		}
		inner := locals
		for _, b := range bs {
			inner = append(append([]string{}, inner...), b.name)
		}
		body, err := ps.expr(inner)
		if err != nil {
			return 0, err
		}
		return ps.wrap(TPi, bs, body), nil
	}
	lhs, err := ps.app(locals)
	if err != nil {
		return 0, err
	}
	if ps.is("→") || ps.is("->") {
		ps.next()
		// non-dependent arrow: the codomain is parsed with an anonymous binder
		rhs, err := ps.expr(append(append([]string{}, locals...), ""))
		if err != nil {
			return 0, err
		}
		return s.Pi(lhs, rhs), nil
	}
	return lhs, nil
}

func (ps *parser) startsAtom() bool {
	t := ps.peek()
	if t.kind == "id" {
		return !keywords[t.s] || t.s == "Prop" || t.s == "Type" || t.s == "Sort"
	}
	return t.kind == "sym" && t.s == "("
}

func (ps *parser) app(locals []string) (int, error) {
	f, err := ps.atom(locals)
	if err != nil {
		return 0, err
	}
	for ps.startsAtom() {
		a, err := ps.atom(locals)
		if err != nil {
			return 0, err
		}
		f = ps.env.S.App(f, a)
	}
	return f, nil
}

func (ps *parser) atom(locals []string) (int, error) {
	s := ps.env.S
	t := ps.peek()
	if t.kind == "sym" && t.s == "(" {
		ps.next()
		e, err := ps.expr(locals)
		if err != nil {
			return 0, err
		}
		return e, ps.expect(")")
	}
	if t.kind != "id" {
		return 0, ps.errf("unexpected %q", t.s)
	}
	ps.next()
	switch t.s {
	case "Prop":
		return s.Sort(0), nil
	case "Type", "Sort":
		lvl := 0
		if ps.peek().kind == "num" {
			n, _ := strconv.Atoi(ps.next().s)
			lvl = n
		} else if t.s == "Sort" {
			return 0, ps.errf("Sort needs a numeric level (no universe polymorphism)")
		}
		if t.s == "Type" {
			lvl++
		}
		return s.Sort(lvl), nil
	}
	for i := len(locals) - 1; i >= 0; i-- {
		if locals[i] == t.s {
			return s.BVar(len(locals) - 1 - i), nil
		}
	}
	if d, ok := ps.env.byNm[t.s]; ok {
		if d.Value < 0 {
			return 0, ps.errf("%s has no body (sorry) and cannot be unfolded", t.s)
		}
		return d.Value, nil
	}
	ps.p--
	return 0, ps.errf("unknown identifier %s", t.s)
}

// PublicSource returns the source with every theorem body replaced by `sorry`.
// This is exactly what a verifier needs to see.
func (e *Env) PublicSource() string {
	var b strings.Builder
	last := 0
	for _, d := range e.Decls {
		if d.Kind != "theorem" {
			continue
		}
		b.WriteString(e.Src[last:d.BodyStart])
		b.WriteString("sorry")
		last = d.BodyEnd
	}
	b.WriteString(e.Src[last:])
	return b.String()
}
