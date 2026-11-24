package kernel

import "fmt"

// The certifying type checker. It is an ordinary bidirectional checker for
// the Calculus of Constructions with inductive constants, except that every
// inference step, every binder opening and every β/ι-conversion step is
// recorded as a row of the certificate tables.

type checker struct {
	s         *Store
	c         *Certificate
	ctxMemo   map[[2]int]int
	lookMemo  map[[2]int]int
	instMemo  map[[3]int]int
	reflMemo  map[int]int
	nfMemo    map[int][2]int
	inferMemo map[[2]int]int
	convMemo  map[[3]int]int
	fuel      int
}

type TypeError struct{ Msg string }

func (e *TypeError) Error() string { return e.Msg }

func (ck *checker) errf(f string, a ...any) error { return &TypeError{fmt.Sprintf(f, a...)} }

func newChecker(s *Store) *checker {
	return &checker{
		s: s, c: &Certificate{S: s, Ctx: []CtxRow{{0, 0, 0}}},
		ctxMemo: map[[2]int]int{}, lookMemo: map[[2]int]int{}, instMemo: map[[3]int]int{},
		reflMemo: map[int]int{}, nfMemo: map[int][2]int{}, inferMemo: map[[2]int]int{},
		convMemo: map[[3]int]int{}, fuel: 1 << 20,
	}
}

// importConsts copies src's constant table (and the terms it refers to) into s.
func importConsts(s, src *Store, memo map[int]int) {
	for _, k := range src.Consts {
		r := k
		r.Type = s.Import(src, k.Type, memo)
		if k.Ctor == 1 {
			r.Rhs = s.Import(src, k.Rhs, memo)
		}
		s.Consts = append(s.Consts, r)
	}
	s.ConstNames = src.ConstNames
}

// PublicLayout lays out the public inputs canonically: row 0 is always Prop,
// then the constant table's terms (types and ι right-hand sides, in constant
// order), then the statement DAG in post-order, then padding. The constant
// table is padded to sz.NK rows. Prover and verifier both call this, so both
// agree on the public inputs.
func PublicLayout(src *Store, stmt int, sz Sizes, memo map[int]int) (*Store, int, error) {
	s := NewStore()
	s.Sort(0)
	if len(src.Consts) > sz.NK {
		return nil, 0, fmt.Errorf("environment has %d constants; circuit capacity NK=%d", len(src.Consts), sz.NK)
	}
	importConsts(s, src, memo)
	root := s.Import(src, stmt, memo)
	if len(s.Nodes) > sz.NP {
		return nil, 0, fmt.Errorf("statement and inductive declarations have %d DAG nodes; circuit capacity NP=%d", len(s.Nodes), sz.NP)
	}
	for len(s.Nodes) < sz.NP {
		s.AppendRaw(Node{})
	}
	// Unused constant rows have type Prop (row 0): at worst they are opaque
	// propositional atoms, which is a conservative extension.
	for len(s.Consts) < sz.NK {
		s.Consts = append(s.Consts, ConstRow{})
	}
	return s, root, nil
}

// Certify type-checks `proof : stmt` (both closed terms in src) and returns the
// unpadded certificate.
func Certify(src *Store, stmt, proof int, sz Sizes) (*Certificate, error) {
	memo := map[int]int{}
	s, root, err := PublicLayout(src, stmt, sz, memo)
	if err != nil {
		return nil, err
	}
	t := s.Import(src, proof, memo)
	ck := newChecker(s)
	c := ck.c
	c.Root = root
	if s.N(t).F != 0 || s.N(t).G != 0 || s.N(root).F != 0 || s.N(root).G != 0 {
		return nil, fmt.Errorf("proof and statement must be closed terms")
	}
	r, err := ck.check(0, t, root)
	if err != nil {
		return nil, err
	}
	if r != len(c.Jud)-1 {
		// the root judgment was memoised earlier (only possible in degenerate
		// cases); re-emit it as a trivial conversion so it is the last row.
		c2, _, err := ck.inferSort(0, root)
		if err != nil {
			return nil, err
		}
		c.Jud = append(c.Jud, JudRow{Rule: JConv, Ctx: 0, Subj: t, Ty: root, C1: r, C2: c2, Cv: ck.refl(root)})
	}
	return c, nil
}

// TypeOf infers the type of a closed term (used by `zklean check`).
func TypeOf(src *Store, t int) (*Store, int, error) {
	s := NewStore()
	s.Sort(0)
	memo := map[int]int{}
	importConsts(s, src, memo)
	tt := s.Import(src, t, memo)
	ck := newChecker(s)
	r, err := ck.infer(0, tt)
	if err != nil {
		return nil, 0, err
	}
	return s, ck.c.Jud[r].Ty, nil
}

// ---- contexts ----

func (ck *checker) push(ctx, a int) int {
	k := [2]int{ctx, a}
	if x, ok := ck.ctxMemo[k]; ok {
		return x
	}
	ck.c.Ctx = append(ck.c.Ctx, CtxRow{Parent: ctx, Type: a, Depth: ck.c.Ctx[ctx].Depth + 1})
	x := len(ck.c.Ctx) - 1
	ck.ctxMemo[k] = x
	return x
}

func (ck *checker) look(ctx, lvl int) (int, error) {
	k := [2]int{ctx, lvl}
	if r, ok := ck.lookMemo[k]; ok {
		return r, nil
	}
	cr := ck.c.Ctx[ctx]
	if ctx == 0 {
		return 0, ck.errf("free variable f%d not in context", lvl)
	}
	var row LookRow
	if lvl == cr.Depth-1 {
		row = LookRow{Ctx: ctx, Lvl: lvl, Ty: cr.Type, Base: 1}
	} else {
		nx, err := ck.look(cr.Parent, lvl)
		if err != nil {
			return 0, err
		}
		row = LookRow{Ctx: ctx, Lvl: lvl, Ty: ck.c.Look[nx].Ty, Next: nx}
	}
	ck.c.Look = append(ck.c.Look, row)
	r := len(ck.c.Look) - 1
	ck.lookMemo[k] = r
	return r, nil
}

// ---- instantiation ----

func (ck *checker) inst(t, k, v int) int {
	key := [3]int{t, k, v}
	if r, ok := ck.instMemo[key]; ok {
		return r
	}
	s := ck.s
	n := s.N(t)
	row := InstRow{T: t, K: k, S: v}
	if n.G <= k && IsComposite(n.Tag) {
		row.R, row.Skip = t, 1
		ck.c.Inst = append(ck.c.Inst, row)
		ck.instMemo[key] = len(ck.c.Inst) - 1
		return len(ck.c.Inst) - 1
	}
	switch n.Tag {
	case TSort, TFVar, TConst:
		row.R = t
	case TBVar:
		if n.A == k {
			row.R = v
		} else {
			row.R = t
		}
	default:
		bk := 0
		if n.Tag != TApp {
			bk = 1
		}
		row.C1 = ck.inst(n.A, k, v)
		row.C2 = ck.inst(n.B, k+bk, v)
		row.R = s.Mk(n.Tag, ck.c.Inst[row.C1].R, ck.c.Inst[row.C2].R)
	}
	ck.c.Inst = append(ck.c.Inst, row)
	r := len(ck.c.Inst) - 1
	ck.instMemo[key] = r
	return r
}

// ---- conversion ----

func (ck *checker) addConv(r ConvRow) int {
	ck.c.Conv = append(ck.c.Conv, r)
	return len(ck.c.Conv) - 1
}

func (ck *checker) refl(t int) int {
	if r, ok := ck.reflMemo[t]; ok {
		return r
	}
	r := ck.addConv(ConvRow{Rule: CRefl, T1: t, T2: t})
	ck.reflMemo[t] = r
	return r
}

func (ck *checker) isRefl(r int) bool { return ck.c.Conv[r].T1 == ck.c.Conv[r].T2 }

func (ck *checker) sym(r int) int {
	cr := ck.c.Conv[r]
	if cr.T1 == cr.T2 {
		return ck.refl(cr.T1)
	}
	return ck.addConv(ConvRow{Rule: CSym, T1: cr.T2, T2: cr.T1, C1: r})
}

func (ck *checker) trans(r1, r2 int) int {
	if ck.isRefl(r1) {
		return r2
	}
	if ck.isRefl(r2) {
		return r1
	}
	a, b := ck.c.Conv[r1], ck.c.Conv[r2]
	if a.T2 != b.T1 {
		panic("trans mismatch")
	}
	return ck.addConv(ConvRow{Rule: CTrans, T1: a.T1, T2: b.T2, C1: r1, C2: r2, M: a.T2})
}

// nf computes the β-normal form n of the locally-closed term t together with
// a conversion row proving t ≡ n.
func (ck *checker) nf(t int) (int, int, error) {
	if v, ok := ck.nfMemo[t]; ok {
		return v[0], v[1], nil
	}
	ck.fuel--
	if ck.fuel < 0 {
		return 0, 0, ck.errf("normalisation fuel exhausted")
	}
	s := ck.s
	n := s.N(t)
	var nt, row int
	switch n.Tag {
	case TSort, TFVar, TConst:
		nt, row = t, ck.refl(t)
	case TBVar:
		return 0, 0, ck.errf("internal: nf of non-locally-closed term")
	case TPi, TLam:
		na, ra, err := ck.nf(n.A)
		if err != nil {
			return 0, 0, err
		}
		x := s.N(n.B).F // fresh: no FVar >= F(b) occurs in b (nor in its normal form)
		v := s.FVar(x)
		i1 := ck.inst(n.B, 0, v)
		bo := ck.c.Inst[i1].R
		nbo, rb, err := ck.nf(bo)
		if err != nil {
			return 0, 0, err
		}
		nb := s.Close(nbo, x, 0)
		nt = s.Mk(n.Tag, na, nb)
		if nt == t {
			row = ck.refl(t)
		} else {
			i2 := ck.inst(nb, 0, v)
			if ck.c.Inst[i2].R != nbo {
				panic("close/open mismatch")
			}
			rule := CPi
			if n.Tag == TLam {
				rule = CLam
			}
			row = ck.addConv(ConvRow{Rule: rule, T1: t, T2: nt, C1: ra, C2: rb, I1: i1, I2: i2, V: v})
		}
	case TApp:
		nf_, rf, err := ck.nf(n.A)
		if err != nil {
			return 0, 0, err
		}
		if s.N(nf_).Tag == TLam {
			redex := s.App(nf_, n.B)
			r1 := ck.refl(t)
			if redex != t {
				r1 = ck.addConv(ConvRow{Rule: CApp, T1: t, T2: redex, C1: rf, C2: ck.refl(n.B)})
			}
			i := ck.inst(s.N(nf_).B, 0, n.B)
			red := ck.c.Inst[i].R
			r2 := ck.addConv(ConvRow{Rule: CBeta, T1: redex, T2: red, I1: i})
			nr, r3, err := ck.nf(red)
			if err != nil {
				return 0, 0, err
			}
			nt, row = nr, ck.trans(ck.trans(r1, r2), r3)
		} else {
			na, ra, err := ck.nf(n.B)
			if err != nil {
				return 0, 0, err
			}
			nt = s.App(nf_, na)
			if nt == t {
				row = ck.refl(t)
			} else {
				row = ck.addConv(ConvRow{Rule: CApp, T1: t, T2: nt, C1: rf, C2: ra})
			}
			if ri, red, ok := ck.iota(nt); ok {
				nr, r3, err := ck.nf(red)
				if err != nil {
					return 0, 0, err
				}
				nt, row = nr, ck.trans(ck.trans(row, ri), r3)
			}
		}
	}
	ck.nfMemo[t] = [2]int{nt, row}
	return nt, row, nil
}

// iota recognises t = rec a_1 … a_NRec (c b_1 … b_NCA) and records the iota
// walk and the CIota conversion row t ≡ Rhs(c) rec a_1 … a_NPre b_{NCP+1} … b_NCA.
func (ck *checker) iota(t int) (row, red int, ok bool) {
	s := ck.s
	h, as := s.Spine(s.N(t).A)
	c, bs := s.Spine(s.N(t).B)
	hn, cn := s.N(h), s.N(c)
	if hn.Tag != TConst || cn.Tag != TConst || cn.A >= len(s.Consts) {
		return 0, 0, false
	}
	k := s.Consts[cn.A]
	if k.Ctor != 1 || k.Rec != hn.A || len(as) != k.NRec || len(bs) != k.NCA {
		return 0, 0, false
	}
	add := func(r IotaRow) int {
		ck.c.Iota = append(ck.c.Iota, r)
		return len(ck.c.Iota) - 1
	}
	u, w := h, s.App(k.Rhs, h)
	prev := add(IotaRow{Kind: WRecBase, Ctor: cn.A, U: u, W: w})
	for i, a := range as {
		u = s.App(u, a)
		keep := 0
		if i < k.NPre {
			keep, w = 1, s.App(w, a)
		}
		prev = add(IotaRow{Kind: WRecArg, Ctor: cn.A, U: u, W: w, N: i + 1, Prev: prev, Keep: keep})
	}
	m := c
	prev = add(IotaRow{Kind: WCtorBase, Ctor: cn.A, U: u, M: m, W: w, Prev: prev})
	for i, b := range bs {
		m = s.App(m, b)
		keep := 0
		if i >= k.NCP {
			keep, w = 1, s.App(w, b)
		}
		prev = add(IotaRow{Kind: WCtorArg, Ctor: cn.A, U: u, M: m, W: w, N: i + 1, Prev: prev, Keep: keep})
	}
	return ck.addConv(ConvRow{Rule: CIota, T1: t, T2: w, I1: prev}), w, true
}

func (ck *checker) defeq(t1, t2 int) (int, error) {
	n1, r1, err := ck.nf(t1)
	if err != nil {
		return 0, err
	}
	n2, r2, err := ck.nf(t2)
	if err != nil {
		return 0, err
	}
	if n1 != n2 {
		return 0, ck.errf("type mismatch:\n  %s\nis not definitionally equal to\n  %s", ck.s.Show(n1), ck.s.Show(n2))
	}
	return ck.trans(r1, ck.sym(r2)), nil
}

// ---- typing ----

func (ck *checker) addJud(r JudRow) int {
	ck.c.Jud = append(ck.c.Jud, r)
	return len(ck.c.Jud) - 1
}

func (ck *checker) depth(ctx int) int { return ck.c.Ctx[ctx].Depth }

func (ck *checker) infer(ctx, t int) (int, error) {
	key := [2]int{ctx, t}
	if r, ok := ck.inferMemo[key]; ok {
		return r, nil
	}
	s := ck.s
	n := s.N(t)
	var row JudRow
	row.Ctx, row.Subj = ctx, t
	switch n.Tag {
	case TSort:
		row.Rule, row.Ty = JSort, s.Sort(n.A+1)
	case TFVar:
		l, err := ck.look(ctx, n.A)
		if err != nil {
			return 0, err
		}
		row.Rule, row.L, row.Ty = JVar, l, ck.c.Look[l].Ty
	case TBVar:
		return 0, ck.errf("internal: loose bound variable")
	case TConst:
		if n.A >= len(s.Consts) {
			return 0, ck.errf("unknown constant c%d", n.A)
		}
		v := s.Sort(n.B)
		i1 := ck.inst(s.Consts[n.A].Type, 0, v)
		row.Rule, row.V, row.I1, row.Ty = JConst, v, i1, ck.c.Inst[i1].R
	case TPi:
		c1, u, err := ck.inferSort(ctx, n.A)
		if err != nil {
			return 0, err
		}
		x := ck.push(ctx, n.A)
		v := s.FVar(ck.depth(ctx))
		i1 := ck.inst(n.B, 0, v)
		c2, w, err := ck.inferSort(x, ck.c.Inst[i1].R)
		if err != nil {
			return 0, err
		}
		m := max(u, w)
		lvl := m
		if w == 0 {
			lvl = 0 // impredicative Prop
		}
		row.Rule, row.C1, row.C2, row.I1, row.X, row.V, row.M, row.Ty = JPi, c1, c2, i1, x, v, m, s.Sort(lvl)
	case TLam:
		x := ck.push(ctx, n.A)
		d := ck.depth(ctx)
		v := s.FVar(d)
		i1 := ck.inst(n.B, 0, v)
		c2, err := ck.infer(x, ck.c.Inst[i1].R)
		if err != nil {
			return 0, err
		}
		bo := ck.c.Jud[c2].Ty
		pi := s.Pi(n.A, s.Close(bo, d, 0))
		c1, _, err := ck.inferSort(ctx, pi)
		if err != nil {
			return 0, err
		}
		i2 := ck.inst(s.N(pi).B, 0, v)
		if ck.c.Inst[i2].R != bo {
			panic("lam: close/open mismatch")
		}
		row.Rule, row.C1, row.C2, row.I1, row.I2, row.X, row.V, row.Ty = JLam, c1, c2, i1, i2, x, v, pi
	case TApp:
		c1, err := ck.inferPi(ctx, n.A)
		if err != nil {
			return 0, err
		}
		p := s.N(ck.c.Jud[c1].Ty)
		c2, err := ck.check(ctx, n.B, p.A)
		if err != nil {
			return 0, err
		}
		i1 := ck.inst(p.B, 0, n.B)
		row.Rule, row.C1, row.C2, row.I1, row.Ty = JApp, c1, c2, i1, ck.c.Inst[i1].R
	}
	r := ck.addJud(row)
	ck.inferMemo[key] = r
	return r, nil
}

// convTo turns judgment r (ctx ⊢ t : T) into ctx ⊢ t : target using conv row cv.
func (ck *checker) convTo(ctx, r, target, cv int) (int, error) {
	key := [3]int{ctx, ck.c.Jud[r].Subj, target}
	if x, ok := ck.convMemo[key]; ok {
		return x, nil
	}
	c2, _, err := ck.inferSort(ctx, target)
	if err != nil {
		return 0, err
	}
	x := ck.addJud(JudRow{Rule: JConv, Ctx: ctx, Subj: ck.c.Jud[r].Subj, Ty: target, C1: r, C2: c2, Cv: cv})
	ck.convMemo[key] = x
	return x, nil
}

func (ck *checker) inferWhnf(ctx, t, tag int, what string) (int, error) {
	r, err := ck.infer(ctx, t)
	if err != nil {
		return 0, err
	}
	ty := ck.c.Jud[r].Ty
	if ck.s.N(ty).Tag == tag {
		return r, nil
	}
	n, cv, err := ck.nf(ty)
	if err != nil {
		return 0, err
	}
	if ck.s.N(n).Tag != tag {
		return 0, ck.errf("expected %s, but\n  %s\nhas type\n  %s", what, ck.s.Show(t), ck.s.Show(n))
	}
	return ck.convTo(ctx, r, n, cv)
}

func (ck *checker) inferSort(ctx, t int) (int, int, error) {
	r, err := ck.inferWhnf(ctx, t, TSort, "a type")
	if err != nil {
		return 0, 0, err
	}
	return r, ck.s.N(ck.c.Jud[r].Ty).A, nil
}

func (ck *checker) inferPi(ctx, t int) (int, error) {
	return ck.inferWhnf(ctx, t, TPi, "a function")
}

func (ck *checker) check(ctx, t, want int) (int, error) {
	r, err := ck.infer(ctx, t)
	if err != nil {
		return 0, err
	}
	got := ck.c.Jud[r].Ty
	if got == want {
		return r, nil
	}
	cv, err := ck.defeq(got, want)
	if err != nil {
		return 0, err
	}
	return ck.convTo(ctx, r, want, cv)
}

// ---- padding ----

// Pad extends every table to the fixed capacities with trivially valid rows and
// moves the root judgment to the last row.
func (c *Certificate) Pad(sz Sizes) error {
	if c.Padded {
		return nil
	}
	s := c.S
	sort1 := s.Sort(1) // needed by padding judgments
	need := map[string][2]int{
		"terms": {len(s.Nodes), sz.NT}, "ctx": {len(c.Ctx) + 1, sz.NX}, "lookups": {len(c.Look), sz.NL},
		"inst": {len(c.Inst), sz.NI}, "conv": {len(c.Conv), sz.NC}, "judgments": {len(c.Jud), sz.NJ},
		"iota": {len(c.Iota), sz.NW},
	}
	for k, v := range need {
		if v[0] > v[1] {
			return fmt.Errorf("certificate needs %d %s rows; circuit capacity is %d (use a larger profile)", v[0], k, v[1])
		}
	}
	for len(s.Nodes) < sz.NT {
		s.AppendRaw(Node{})
	}
	for len(c.Ctx) < sz.NX {
		c.Ctx = append(c.Ctx, CtxRow{Parent: 0, Type: 0, Depth: 1})
	}
	for len(c.Look) < sz.NL {
		c.Look = append(c.Look, LookRow{Ctx: 1, Lvl: c.Ctx[1].Depth - 1, Ty: c.Ctx[1].Type, Base: 1})
	}
	for len(c.Iota) < sz.NW {
		c.Iota = append(c.Iota, IotaRow{Kind: WPad})
	}
	for len(c.Inst) < sz.NI {
		c.Inst = append(c.Inst, InstRow{})
	}
	if len(c.Conv) == 0 {
		c.Conv = append(c.Conv, ConvRow{Rule: CRefl})
	}
	for len(c.Conv) < sz.NC {
		c.Conv = append(c.Conv, ConvRow{Rule: CRefl})
	}
	root := c.Jud[len(c.Jud)-1]
	c.Jud = c.Jud[:len(c.Jud)-1]
	for len(c.Jud) < sz.NJ-1 {
		c.Jud = append(c.Jud, JudRow{Rule: JSort, Ctx: 0, Subj: 0, Ty: sort1})
	}
	c.Jud = append(c.Jud, root)
	c.Padded = true
	return nil
}
