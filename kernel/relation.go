package kernel

import "fmt"

// Relation checks the padded certificate against exactly the constraints that
// the circuit enforces (circuit/circuit.go mirrors this function line by line).
// It is the specification of the ZK statement:
//
//	∃ witness tables W.  Relation(PublicRows, Root, W) holds
//
// and the soundness claim is: Relation holds  ⇒  ∃ closed t. ⊢ t : Root.
// It uses integer semantics where the circuit uses field semantics; the range
// checks make the two coincide (all compared quantities are < 2^NB ≪ p).
func (c *Certificate) Relation(sz Sizes) (retErr error) {
	// an out-of-range index is a failed lookup in the circuit
	defer func() {
		if r := recover(); r != nil {
			retErr = fmt.Errorf("lookup out of range: %v", r)
		}
	}()
	s := c.S
	T := s.Nodes
	lim := 1 << sz.NB
	rng := func(x int) bool { return x >= 0 && x < lim }
	var err error
	fail := func(f string, a ...any) {
		if err == nil {
			err = fmt.Errorf(f, a...)
		}
	}
	b2i := func(b bool) int {
		if b {
			return 1
		}
		return 0
	}
	if len(T) != sz.NT || len(c.Ctx) != sz.NX || len(c.Look) != sz.NL || len(c.Inst) != sz.NI ||
		len(c.Conv) != sz.NC || len(c.Jud) != sz.NJ || len(s.Consts) != sz.NK || len(c.Iota) != sz.NW {
		return fmt.Errorf("certificate not padded to sizes")
	}
	K := s.Consts // public
	inT := func(i int) bool { return i >= 0 && i < sz.NT }

	// ---- terms ----
	for i, n := range T {
		if n.Tag < 0 || n.Tag >= NumTags {
			fail("term %d: bad tag", i)
			continue
		}
		comp := IsComposite(n.Tag)
		binder := n.Tag == TPi || n.Tag == TLam
		if !rng(n.A) || !rng(n.B) || !rng(n.F) || !rng(n.G) {
			fail("term %d: field out of range", i)
			continue
		}
		var fa, fb, ga, gb int
		if comp {
			if !(n.A < i && n.B < i) {
				fail("term %d: children must precede", i)
				continue
			}
			fa, fb, ga, gb = T[n.A].F, T[n.B].F, T[n.A].G, T[n.B].G
		}
		if !rng(n.F-fa) || !rng(n.F-fb) || !rng(n.F-b2i(n.Tag == TFVar)*(n.A+1)) {
			fail("term %d: F bound", i)
		}
		if !rng(n.G-ga) || !rng(n.G+b2i(binder)-gb) || !rng(n.G-b2i(n.Tag == TBVar)*(n.A+1)) {
			fail("term %d: G bound", i)
		}
	}
	if err != nil {
		return err
	}
	// ---- contexts ----
	X := c.Ctx
	if X[0].Parent != 0 || X[0].Type != 0 || X[0].Depth != 0 {
		return fmt.Errorf("ctx 0 must be empty")
	}
	for x := 1; x < len(X); x++ {
		if !(X[x].Parent >= 0 && X[x].Parent < x) || X[x].Depth != X[X[x].Parent].Depth+1 || !rng(X[x].Depth) {
			return fmt.Errorf("ctx %d malformed", x)
		}
	}
	inX := func(i int) bool { return i >= 0 && i < sz.NX }
	// ---- context lookups ----
	L := c.Look
	for l, r := range L {
		if !inX(r.Ctx) || !(r.Base == 0 || r.Base == 1) {
			return fmt.Errorf("lookup %d malformed", l)
		}
		d := X[r.Ctx].Depth
		if r.Base == 1 {
			if r.Lvl != d-1 || !rng(d-1) || r.Ty != X[r.Ctx].Type {
				return fmt.Errorf("lookup %d: bad base case", l)
			}
		} else {
			if !(r.Next >= 0 && r.Next < l) {
				return fmt.Errorf("lookup %d: next must precede", l)
			}
			nx := L[r.Next]
			if nx.Ctx != X[r.Ctx].Parent || nx.Lvl != r.Lvl || nx.Ty != r.Ty {
				return fmt.Errorf("lookup %d: bad step", l)
			}
		}
	}
	// ---- instantiation ----
	I := c.Inst
	for k, r := range I {
		if !inT(r.T) || !inT(r.S) || !inT(r.R) {
			return fmt.Errorf("inst %d: index out of range", k)
		}
		n := T[r.T]
		if T[r.S].G != 0 || !(r.Skip == 0 || r.Skip == 1) {
			return fmt.Errorf("inst %d: substituted term not locally closed", k)
		}
		if r.Skip == 1 {
			if !rng(r.K-n.G) || r.R != r.T {
				return fmt.Errorf("inst %d: bad skip", k)
			}
			continue
		}
		switch n.Tag {
		case TSort, TFVar, TConst:
			if r.R != r.T {
				return fmt.Errorf("inst %d: atom", k)
			}
		case TBVar:
			want := r.T
			if n.A == r.K {
				want = r.S
			}
			if r.R != want {
				return fmt.Errorf("inst %d: bvar", k)
			}
		default:
			bk := b2i(n.Tag != TApp)
			if T[r.R].Tag != n.Tag || !(r.C1 >= 0 && r.C1 < k) || !(r.C2 >= 0 && r.C2 < k) {
				return fmt.Errorf("inst %d: composite shape", k)
			}
			a, b := I[r.C1], I[r.C2]
			if a.T != n.A || a.K != r.K || a.S != r.S || a.R != T[r.R].A ||
				b.T != n.B || b.K != r.K+bk || b.S != r.S || b.R != T[r.R].B {
				return fmt.Errorf("inst %d: children", k)
			}
		}
	}
	// ---- iota walks ----
	W := c.Iota
	for k, r := range W {
		if r.Kind < 0 || r.Kind >= NumWKinds || !inT(r.U) || !inT(r.M) || !inT(r.W) || !rng(r.N) ||
			!(r.Keep == 0 || r.Keep == 1) {
			return fmt.Errorf("iota %d malformed", k)
		}
		if r.Kind == WPad {
			continue
		}
		kr := K[r.Ctor]
		u, m, w := T[r.U], T[r.M], T[r.W]
		ok := true
		if r.Kind == WRecBase {
			ok = kr.Ctor == 1 && u.Tag == TConst && u.A == kr.Rec && w.Tag == TApp && w.A == kr.Rhs && w.B == r.U && r.N == 0
		} else {
			if !(r.Prev >= 0 && r.Prev < k) {
				return fmt.Errorf("iota %d: prev must precede", k)
			}
			p := W[r.Prev]
			ok = p.Ctor == r.Ctor
			// keep ⇔ argument N goes into the right-hand side
			keepW := (w.Tag == TApp && w.A == p.W) && r.Keep == 1 || r.W == p.W && r.Keep == 0
			switch r.Kind {
			case WRecArg:
				ok = ok && (p.Kind == WRecBase || p.Kind == WRecArg) && u.Tag == TApp && u.A == p.U && r.N == p.N+1 &&
					(r.Keep == 1 && rng(kr.NPre-p.N-1) || r.Keep == 0 && rng(p.N-kr.NPre)) &&
					keepW && (r.Keep == 0 || w.B == u.B)
			case WCtorBase:
				ok = ok && (p.Kind == WRecBase || p.Kind == WRecArg) && p.N == kr.NRec && r.U == p.U && r.W == p.W &&
					m.Tag == TConst && m.A == r.Ctor && r.N == 0
			case WCtorArg:
				ok = ok && (p.Kind == WCtorBase || p.Kind == WCtorArg) && r.U == p.U && m.Tag == TApp && m.A == p.M &&
					r.N == p.N+1 && (r.Keep == 1 && rng(p.N-kr.NCP) || r.Keep == 0 && rng(kr.NCP-p.N-1)) &&
					keepW && (r.Keep == 0 || w.B == m.B)
			}
		}
		if !ok {
			return fmt.Errorf("iota %d (kind %d) invalid", k, r.Kind)
		}
	}
	// ---- conversion ----
	C := c.Conv
	for k, r := range C {
		if !inT(r.T1) || !inT(r.T2) || r.Rule < 0 || r.Rule >= NumCRules {
			return fmt.Errorf("conv %d malformed", k)
		}
		t1, t2 := T[r.T1], T[r.T2]
		if t1.G != 0 || t2.G != 0 {
			return fmt.Errorf("conv %d: terms must be locally closed", k)
		}
		uses1 := r.Rule != CRefl && r.Rule != CBeta && r.Rule != CIota
		uses2 := uses1 && r.Rule != CSym
		if uses1 && !(r.C1 >= 0 && r.C1 < k) || uses2 && !(r.C2 >= 0 && r.C2 < k) {
			return fmt.Errorf("conv %d: children must precede", k)
		}
		c1, c2 := C[r.C1], C[r.C2]
		ok := true
		switch r.Rule {
		case CRefl:
			ok = r.T1 == r.T2
		case CSym:
			ok = c1.T1 == r.T2 && c1.T2 == r.T1
		case CTrans:
			ok = c1.T1 == r.T1 && c1.T2 == r.M && c2.T1 == r.M && c2.T2 == r.T2
		case CBeta:
			i := I[r.I1]
			ok = t1.Tag == TApp && T[t1.A].Tag == TLam && i.T == T[t1.A].B && i.K == 0 && i.S == t1.B && i.R == r.T2
		case CPi, CLam:
			tag := TPi
			if r.Rule == CLam {
				tag = TLam
			}
			v := T[r.V]
			i1, i2 := I[r.I1], I[r.I2]
			ok = t1.Tag == tag && t2.Tag == tag && c1.T1 == t1.A && c1.T2 == t2.A &&
				v.Tag == TFVar && rng(v.A-T[t1.B].F) && rng(v.A-T[t2.B].F) &&
				i1.T == t1.B && i1.K == 0 && i1.S == r.V && i2.T == t2.B && i2.K == 0 && i2.S == r.V &&
				c2.T1 == i1.R && c2.T2 == i2.R
		case CApp:
			ok = t1.Tag == TApp && t2.Tag == TApp && c1.T1 == t1.A && c1.T2 == t2.A && c2.T1 == t1.B && c2.T2 == t2.B
		case CIota:
			w := W[r.I1]
			ok = (w.Kind == WCtorBase || w.Kind == WCtorArg) && w.N == K[w.Ctor].NCA &&
				t1.Tag == TApp && t1.A == w.U && t1.B == w.M && r.T2 == w.W
		}
		if !ok {
			return fmt.Errorf("conv %d (rule %d) invalid", k, r.Rule)
		}
	}
	// ---- judgments ----
	J := c.Jud
	for j, r := range J {
		if !inX(r.Ctx) || !inT(r.Subj) || !inT(r.Ty) || r.Rule < 0 || r.Rule >= NumJRules {
			return fmt.Errorf("jud %d malformed", j)
		}
		sb, ty := T[r.Subj], T[r.Ty]
		d := X[r.Ctx].Depth
		if !rng(d-sb.F) || !rng(d-ty.F) || sb.G != 0 || ty.G != 0 {
			return fmt.Errorf("jud %d: terms not well-scoped", j)
		}
		uses := r.Rule == JPi || r.Rule == JLam || r.Rule == JApp || r.Rule == JConv
		if uses && !(r.C1 >= 0 && r.C1 < j && r.C2 >= 0 && r.C2 < j) {
			return fmt.Errorf("jud %d: children must precede", j)
		}
		c1, c2 := J[r.C1], J[r.C2]
		y1, y2 := T[c1.Ty], T[c2.Ty]
		xr := X[r.X]
		v := T[r.V]
		i1, i2 := I[r.I1], I[r.I2]
		ok := true
		switch r.Rule {
		case JSort:
			ok = sb.Tag == TSort && ty.Tag == TSort && ty.A == sb.A+1
		case JVar:
			lr := L[r.L]
			ok = sb.Tag == TFVar && lr.Ctx == r.Ctx && lr.Lvl == sb.A && lr.Ty == r.Ty
		case JPi, JLam:
			ok = xr.Parent == r.Ctx && xr.Type == sb.A && v.Tag == TFVar && v.A == d &&
				i1.T == sb.B && i1.K == 0 && i1.S == r.V && c2.Ctx == r.X && c2.Subj == i1.R && c1.Ctx == r.Ctx
			if r.Rule == JPi {
				u, w, m := y1.A, y2.A, r.M
				want := m
				if w == 0 {
					want = 0
				}
				ok = ok && sb.Tag == TPi && c1.Subj == sb.A && y1.Tag == TSort && y2.Tag == TSort &&
					rng(m-u) && rng(m-w) && (m-u)*(m-w) == 0 && ty.Tag == TSort && ty.A == want
			} else {
				ok = ok && sb.Tag == TLam && ty.Tag == TPi && ty.A == sb.A && c1.Subj == r.Ty && y1.Tag == TSort &&
					i2.T == ty.B && i2.K == 0 && i2.S == r.V && c2.Ty == i2.R
			}
		case JApp:
			ok = sb.Tag == TApp && c1.Ctx == r.Ctx && c1.Subj == sb.A && y1.Tag == TPi &&
				c2.Ctx == r.Ctx && c2.Subj == sb.B && c2.Ty == y1.A &&
				i1.T == y1.B && i1.K == 0 && i1.S == sb.B && i1.R == r.Ty
		case JConst:
			ok = sb.Tag == TConst && v.Tag == TSort && v.A == sb.B &&
				i1.T == K[sb.A].Type && i1.K == 0 && i1.S == r.V && i1.R == r.Ty
		case JConv:
			cv := C[r.Cv]
			ok = c1.Ctx == r.Ctx && c1.Subj == r.Subj && cv.T1 == c1.Ty && cv.T2 == r.Ty &&
				c2.Ctx == r.Ctx && c2.Subj == r.Ty && y2.Tag == TSort
		}
		if !ok {
			return fmt.Errorf("jud %d (rule %d) invalid", j, r.Rule)
		}
	}
	root := J[len(J)-1]
	if root.Ctx != 0 || root.Ty != c.Root {
		return fmt.Errorf("root judgment does not conclude the statement")
	}
	return nil
}
