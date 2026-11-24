package kernel

import "fmt"

// Inductive declarations.
//
// An inductive family
//
//	inductive I (ps : Ps) : ∀ (is : Is), Sort s where
//	  | c (fs : Fs) : I ps ι(fs)
//
// adds the constants I, I.c (for every constructor) and I.rec to the public
// constant table:
//
//	I.rec.{u} : ∀ ps (motive : ∀ is, I ps is → Sort u)
//	              (minor_c : ∀ fs ihs, motive ι(fs) (I.c ps fs))…
//	              is (t : I ps is), motive is t
//
// with one induction hypothesis ih : ∀ ys, motive ι'(ys) (f ys) per recursive
// field f : ∀ ys, I ps ι'(ys). Each constructor also gets its ι-rule
//
//	I.rec ps P ms is (I.c ps' fs)  ≡  ms_c fs (fun ys => I.rec ps P ms ι'(ys) (f ys))…
//
// stored as a closed right-hand side Rhs_c = fun r ps P ms fs => …, where r
// stands for the recursor itself (so Rhs_c does not depend on u).
//
// Everything here runs on public data: the verifier re-runs it on the public
// file and so trusts its own copy of the constant table. The checks are
// Lean's: well-typed former and constructor types, parameters passed through
// unchanged, strict positivity of recursive occurrences, constructor fields
// living in a universe no larger than the inductive's (unless it is a Prop),
// and large elimination of a Prop only for "syntactic subsingletons" (no
// constructors, or one constructor whose fields are all proofs or appear as
// indices of its result type). Mutual and nested inductives are not supported.

// lb is a binder opened as a free variable of level lvl.
type lb struct{ lvl, ty int }

// abs closes the binders bs (outermost first) over body.
func (s *Store) abs(tag int, bs []lb, body int) int {
	for i := len(bs) - 1; i >= 0; i-- {
		body = s.Mk(tag, bs[i].ty, s.Close(body, bs[i].lvl, 0))
	}
	return body
}

func (s *Store) vars(bs []lb) []int {
	out := make([]int, len(bs))
	for i, b := range bs {
		out[i] = s.FVar(b.lvl)
	}
	return out
}

func cat(xs ...[]lb) []lb {
	var out []lb
	for _, x := range xs {
		out = append(out, x...)
	}
	return out
}

func cati(xs ...[]int) []int {
	var out []int
	for _, x := range xs {
		out = append(out, x...)
	}
	return out
}

// mentions reports whether constant k occurs in t.
func (s *Store) mentions(t, k int) bool {
	memo := map[int]bool{}
	var occ func(int) bool
	occ = func(t int) bool {
		if v, ok := memo[t]; ok {
			return v
		}
		n := s.Nodes[t]
		r := n.Tag == TConst && n.A == k || IsComposite(n.Tag) && (occ(n.A) || occ(n.B))
		memo[t] = r
		return r
	}
	return occ(t)
}

type indField struct {
	rec       bool // recursive occurrence (strictly positive)
	prop      bool // the field is a proof
	inIndices bool // the field appears as an index of the constructor's result
}

type indCtor struct {
	ty     int // normalised closed type, including the parameters
	fields []indField
}

// addInductive elaborates an inductive whose type former has already been
// registered as constant k0 (with its unnormalised type), np parameters, and
// the given constructors (closed types, parameters included).
func (e *Env) addInductive(k0, np int, cnames []string, ctys []int) error {
	s := e.S
	ck := newChecker(s)
	name := s.ConstNames[k0]
	I := s.Const(k0, 0)
	former := s.Consts[k0].Type

	// ---- the type former ----
	if _, _, err := ck.inferSort(0, former); err != nil {
		return fmt.Errorf("ill-typed type: %v", err)
	}
	fT, _, err := ck.nf(former)
	if err != nil {
		return err
	}
	s.Consts[k0].Type = fT
	var paramTys []int
	t := fT
	pctx := 0
	for i := 0; i < np; i++ {
		n := s.N(t)
		paramTys = append(paramTys, n.A)
		pctx = ck.push(pctx, n.A)
		t = s.Inst(n.B, 0, s.FVar(i))
	}
	nidx := 0
	for s.N(t).Tag == TPi {
		t = s.Inst(s.N(t).B, 0, s.FVar(np+nidx))
		nidx++
	}
	if s.N(t).Tag != TSort {
		return fmt.Errorf("type must end in a Sort")
	}
	sortLvl := s.N(t).A

	// checkResult checks that t = I ps' is' with ps' the parameter variables pv
	// and indices not mentioning I, and returns the index arguments.
	checkResult := func(t int, pv []int, what string) ([]int, error) {
		h, args := s.Spine(t)
		if s.N(h).Tag != TConst || s.N(h).A != k0 || len(args) != np+nidx {
			return nil, fmt.Errorf("%s must be an application of %s to %d arguments, got %s", what, name, np+nidx, s.Show(t))
		}
		for i := 0; i < np; i++ {
			if args[i] != pv[i] {
				return nil, fmt.Errorf("%s must pass the parameters of %s unchanged", what, name)
			}
		}
		for _, a := range args[np:] {
			if s.mentions(a, k0) {
				return nil, fmt.Errorf("%s: %s occurs in an index (non-positive occurrence)", what, name)
			}
		}
		return args[np:], nil
	}

	// ---- constructors ----
	pv0 := make([]int, np)
	for i := range pv0 {
		pv0[i] = s.FVar(i)
	}
	scratch := 1 << 20 // free-variable levels for inspection only
	var ctors []indCtor
	for ci, cty := range ctys {
		cname := cnames[ci]
		if _, _, err := ck.inferSort(0, cty); err != nil {
			return fmt.Errorf("constructor %s: ill-typed type: %v", cname, err)
		}
		nty, _, err := ck.nf(cty)
		if err != nil {
			return err
		}
		t := nty
		for i := 0; i < np; i++ {
			n := s.N(t)
			if n.Tag != TPi || n.A != paramTys[i] {
				return fmt.Errorf("constructor %s must take the parameters of %s", cname, name)
			}
			t = s.Inst(n.B, 0, pv0[i])
		}
		ctx := pctx
		var fields []indField
		for s.N(t).Tag == TPi {
			n := s.N(t)
			dom := n.A
			d := np + len(fields)
			_, v, err := ck.inferSort(ctx, dom)
			if err != nil {
				return fmt.Errorf("constructor %s: %v", cname, err)
			}
			if sortLvl != 0 && v > sortLvl {
				return fmt.Errorf("constructor %s: field %d lives in Sort %d, too large for %s : Sort %d",
					cname, len(fields)+1, v, name, sortLvl)
			}
			f := indField{prop: v == 0}
			if s.mentions(dom, k0) {
				// strictly positive: ∀ ys, I ps is' with I not in the ys
				u := dom
				for s.N(u).Tag == TPi {
					if s.mentions(s.N(u).A, k0) {
						return fmt.Errorf("constructor %s: %s occurs to the left of an arrow (not strictly positive)", cname, name)
					}
					u = s.Inst(s.N(u).B, 0, s.FVar(scratch))
					scratch++
				}
				if _, err := checkResult(u, pv0, fmt.Sprintf("constructor %s: recursive field", cname)); err != nil {
					return err
				}
				f.rec = true
			}
			fields = append(fields, f)
			ctx = ck.push(ctx, dom)
			t = s.Inst(n.B, 0, s.FVar(d))
		}
		idx, err := checkResult(t, pv0, fmt.Sprintf("constructor %s: result type", cname))
		if err != nil {
			return err
		}
		for _, a := range idx {
			if n := s.N(a); n.Tag == TFVar && n.A >= np {
				fields[n.A-np].inIndices = true
			}
		}
		ctors = append(ctors, indCtor{ty: nty, fields: fields})
	}
	nc := len(ctors)
	large := sortLvl != 0 || nc == 0
	if sortLvl == 0 && nc == 1 {
		large = true
		for _, f := range ctors[0].fields {
			if !f.prop && !f.inIndices {
				large = false
			}
		}
	}
	kRec := k0 + 1 + nc

	// ---- register constructors and the recursor ----
	for ci, c := range ctors {
		s.Consts = append(s.Consts, ConstRow{Type: c.ty, Ctor: 1, Rec: kRec,
			NPre: np + 1 + nc, NRec: np + 1 + nc + nidx, NCP: np, NCA: np + len(c.fields)})
		s.ConstNames = append(s.ConstNames, cnames[ci])
		e.constIdx[cnames[ci]] = k0 + 1 + ci
	}
	s.Consts = append(s.Consts, ConstRow{})
	s.ConstNames = append(s.ConstNames, name+".rec")
	e.constIdx[name+".rec"] = kRec
	e.recLarge[kRec] = large

	fresh := 0
	newLvl := func() int { fresh++; return fresh - 1 }
	// openWith instantiates the first len(args) binders of t with args and
	// opens the remaining Π binders with fresh variables.
	openWith := func(t int, args []int) ([]lb, int) {
		for _, a := range args {
			t = s.Inst(s.N(t).B, 0, a)
		}
		var bs []lb
		for s.N(t).Tag == TPi {
			l := newLvl()
			bs = append(bs, lb{l, s.N(t).A})
			t = s.Inst(s.N(t).B, 0, s.FVar(l))
		}
		return bs, t
	}
	openParams := func() []lb {
		var ps []lb
		t := fT
		for i := 0; i < np; i++ {
			l := newLvl()
			ps = append(ps, lb{l, s.N(t).A})
			t = s.Inst(s.N(t).B, 0, s.FVar(l))
		}
		return ps
	}
	idxArgs := func(t int) []int { _, a := s.Spine(t); return a[np:] }

	buildRec := func(sortU int) int {
		ps := openParams()
		pv := s.vars(ps)
		ibs, _ := openWith(fT, pv)
		majM := lb{newLvl(), s.Apps(I, cati(pv, s.vars(ibs))...)}
		mot := lb{newLvl(), s.abs(TPi, cat(ibs, []lb{majM}), sortU)}
		mv := s.FVar(mot.lvl)
		var minors []lb
		for ci, c := range ctors {
			fs, res := openWith(c.ty, pv)
			var ihs []lb
			for fi, f := range fs {
				if !c.fields[fi].rec {
					continue
				}
				ys, b := openWith(f.ty, nil)
				ihTy := s.abs(TPi, ys, s.App(s.Apps(mv, idxArgs(b)...), s.Apps(s.FVar(f.lvl), s.vars(ys)...)))
				ihs = append(ihs, lb{newLvl(), ihTy})
			}
			cterm := s.Apps(s.Const(k0+1+ci, 0), cati(pv, s.vars(fs))...)
			minors = append(minors, lb{newLvl(), s.abs(TPi, cat(fs, ihs), s.App(s.Apps(mv, idxArgs(res)...), cterm))})
		}
		is, _ := openWith(fT, pv)
		maj := lb{newLvl(), s.Apps(I, cati(pv, s.vars(is))...)}
		body := s.App(s.Apps(mv, s.vars(is)...), s.FVar(maj.lvl))
		return s.abs(TPi, cat(ps, []lb{mot}, minors, is, []lb{maj}), body)
	}
	var tmpl int
	levels := []int{0}
	if large {
		ph := newLvl()
		tmpl = s.Close(buildRec(s.FVar(ph)), ph, 0)
		levels = []int{0, 1, 2}
	} else {
		tmpl = buildRec(s.Sort(0))
	}
	if s.N(tmpl).F != 0 || s.N(tmpl).G > 1 {
		panic("recursor template not closed")
	}
	s.Consts[kRec].Type = tmpl
	for _, u := range levels {
		rt := s.Inst(tmpl, 0, s.Sort(u))
		if _, _, err := ck.inferSort(0, rt); err != nil {
			return fmt.Errorf("internal: generated recursor is ill-typed: %v", err)
		}
	}

	// ---- ι right-hand sides ----
	prop := s.Sort(0)
	for ci, c := range ctors {
		r := lb{newLvl(), prop}
		ps := make([]lb, np)
		for i := range ps {
			ps[i] = lb{newLvl(), prop}
		}
		pv := s.vars(ps)
		mot := lb{newLvl(), prop}
		ms := make([]lb, nc)
		for i := range ms {
			ms[i] = lb{newLvl(), prop}
		}
		fs, _ := openWith(c.ty, pv)
		var ihs []int
		for fi, f := range fs {
			if !c.fields[fi].rec {
				continue
			}
			ys, b := openWith(f.ty, nil)
			call := s.Apps(s.FVar(r.lvl), cati(pv, []int{s.FVar(mot.lvl)}, s.vars(ms), idxArgs(b))...)
			ihs = append(ihs, s.abs(TLam, ys, s.App(call, s.Apps(s.FVar(f.lvl), s.vars(ys)...))))
		}
		body := s.Apps(s.FVar(ms[ci].lvl), cati(s.vars(fs), ihs)...)
		rhs := s.abs(TLam, cat([]lb{r}, ps, []lb{mot}, ms, fs), body)
		if s.N(rhs).F != 0 || s.N(rhs).G != 0 {
			panic("iota rhs not closed")
		}
		s.Consts[k0+1+ci].Rhs = rhs
	}
	return nil
}

// Constants lists the constants an inductive declaration added, e.g.
// [Nat Nat.zero Nat.succ Nat.rec.{u}].
func (e *Env) Constants(name string) []string {
	k0, ok := e.constIdx[name]
	if !ok {
		return nil
	}
	var out []string
	for k := k0; k < len(e.S.ConstNames); k++ {
		n := e.S.ConstNames[k]
		if large, isRec := e.recLarge[k]; isRec {
			if large {
				n += ".{u}"
			}
			return append(out, n)
		}
		out = append(out, n)
	}
	return out
}
