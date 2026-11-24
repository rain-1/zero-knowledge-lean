// Package circuit encodes kernel.(*Certificate).Relation as an R1CS over
// BN254. Every table is a set of columns inserted into log-derivative lookup
// tables, so each "row i refers to row j" costs O(1) constraints. Range checks
// (for ordering, freshness and universe comparisons) use gnark's
// commitment-based range checker.
//
// Public inputs: the public term rows (tag, a, b for rows 0..NP-1: the
// constant table's terms and the theorem statement), the constant table
// generated from the inductive declarations, and the id of the statement.
// Everything else is private.
package circuit

import (
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/lookup/logderivlookup"
	"github.com/consensys/gnark/std/rangecheck"
	"github.com/river/zklean/kernel"
)

type V = frontend.Variable

type Circuit struct {
	// ---- public ----
	PubTag []V `gnark:",public"`
	PubA   []V `gnark:",public"`
	PubB   []V `gnark:",public"`
	Root   V   `gnark:",public"`

	KType, KCtor, KRec, KRhs, KNPre, KNRec, KNCP, KNCA []V `gnark:",public"`

	// ---- private ----
	Tag, A, B []V // term rows NP..NT-1
	F, G      []V // all NT term rows

	XParent, XType, XDepth []V

	LCtx, LLvl, LTy, LBase, LNext []V

	IT, IK, IS, IR, IC1, IC2, ISkip []V

	CRule, CT1, CT2, CC1, CC2, CI1, CI2, CV, CM []V

	JRule, JCtx, JSubj, JTy, JC1, JC2, JI1, JI2, JX, JV, JL, JCv, JM []V

	WKind, WCtor, WU, WM, WW, WN, WPrev, WKeep []V

	Sz kernel.Sizes `gnark:"-"`
}

func mk(n int) []V { return make([]V, n) }

// New allocates an empty circuit of the given capacities (for compilation).
func New(sz kernel.Sizes) *Circuit {
	c := &Circuit{Sz: sz}
	c.PubTag, c.PubA, c.PubB = mk(sz.NP), mk(sz.NP), mk(sz.NP)
	np := sz.NT - sz.NP
	c.Tag, c.A, c.B = mk(np), mk(np), mk(np)
	c.F, c.G = mk(sz.NT), mk(sz.NT)
	c.XParent, c.XType, c.XDepth = mk(sz.NX), mk(sz.NX), mk(sz.NX)
	c.LCtx, c.LLvl, c.LTy, c.LBase, c.LNext = mk(sz.NL), mk(sz.NL), mk(sz.NL), mk(sz.NL), mk(sz.NL)
	c.IT, c.IK, c.IS, c.IR, c.IC1, c.IC2, c.ISkip = mk(sz.NI), mk(sz.NI), mk(sz.NI), mk(sz.NI), mk(sz.NI), mk(sz.NI), mk(sz.NI)
	for _, p := range []*[]V{&c.CRule, &c.CT1, &c.CT2, &c.CC1, &c.CC2, &c.CI1, &c.CI2, &c.CV, &c.CM} {
		*p = mk(sz.NC)
	}
	for _, p := range []*[]V{&c.JRule, &c.JCtx, &c.JSubj, &c.JTy, &c.JC1, &c.JC2, &c.JI1, &c.JI2, &c.JX, &c.JV, &c.JL, &c.JCv, &c.JM} {
		*p = mk(sz.NJ)
	}
	for _, p := range []*[]V{&c.KType, &c.KCtor, &c.KRec, &c.KRhs, &c.KNPre, &c.KNRec, &c.KNCP, &c.KNCA} {
		*p = mk(sz.NK)
	}
	for _, p := range []*[]V{&c.WKind, &c.WCtor, &c.WU, &c.WM, &c.WW, &c.WN, &c.WPrev, &c.WKeep} {
		*p = mk(sz.NW)
	}
	return c
}

type table struct{ t logderivlookup.Table }

func newTable(api frontend.API, col []V) table {
	t := logderivlookup.New(api)
	for _, v := range col {
		t.Insert(v)
	}
	return table{t}
}
func (t table) at(i V) V { return t.t.Lookup(i)[0] }

func (c *Circuit) Define(api frontend.API) error {
	sz := c.Sz
	rc := rangecheck.New(api)
	rng := func(x V) { rc.Check(x, sz.NB) }
	// constraint helpers, all gated by a boolean selector
	eqIf := func(sel, a, b V) { api.AssertIsEqual(api.Mul(sel, api.Sub(a, b)), 0) }
	geIf := func(sel, a, b V) { rng(api.Mul(sel, api.Sub(a, b))) }    // a >= b
	ltIf := func(sel, a, b V) { rng(api.Mul(sel, api.Sub(b, a, 1))) } // a <  b
	onehot := func(code V, n int) []V {
		s := make([]V, n)
		sum := V(0)
		for k := 0; k < n; k++ {
			s[k] = api.IsZero(api.Sub(code, k))
			sum = api.Add(sum, s[k])
		}
		api.AssertIsEqual(sum, 1)
		return s
	}

	// ---------------- term table ----------------
	tag, a, b := mk(sz.NT), mk(sz.NT), mk(sz.NT)
	for i := 0; i < sz.NT; i++ {
		if i < sz.NP {
			tag[i], a[i], b[i] = c.PubTag[i], c.PubA[i], c.PubB[i]
		} else {
			tag[i], a[i], b[i] = c.Tag[i-sz.NP], c.A[i-sz.NP], c.B[i-sz.NP]
		}
	}
	tTag, tA, tB := newTable(api, tag), newTable(api, a), newTable(api, b)
	tF, tG := newTable(api, c.F), newTable(api, c.G)

	for i := 0; i < sz.NT; i++ {
		s := onehot(tag[i], kernel.NumTags)
		comp := api.Add(s[kernel.TPi], s[kernel.TLam], s[kernel.TApp])
		binder := api.Add(s[kernel.TPi], s[kernel.TLam])
		rng(a[i])
		rng(b[i])
		rng(c.F[i])
		rng(c.G[i])
		ltIf(comp, a[i], i)
		ltIf(comp, b[i], i)
		ia, ib := api.Mul(comp, a[i]), api.Mul(comp, b[i])
		fa, fb, ga, gb := tF.at(ia), tF.at(ib), tG.at(ia), tG.at(ib)
		geIf(1, c.F[i], api.Mul(comp, fa))
		geIf(1, c.F[i], api.Mul(comp, fb))
		geIf(1, c.F[i], api.Mul(s[kernel.TFVar], api.Add(a[i], 1)))
		geIf(1, c.G[i], api.Mul(comp, ga))
		geIf(1, api.Add(c.G[i], binder), api.Mul(comp, gb))
		geIf(1, c.G[i], api.Mul(s[kernel.TBVar], api.Add(a[i], 1)))
	}

	// ---------------- contexts ----------------
	api.AssertIsEqual(c.XParent[0], 0)
	api.AssertIsEqual(c.XType[0], 0)
	api.AssertIsEqual(c.XDepth[0], 0)
	xPar, xTyp, xDep := newTable(api, c.XParent), newTable(api, c.XType), newTable(api, c.XDepth)
	for x := 1; x < sz.NX; x++ {
		ltIf(1, c.XParent[x], x)
		api.AssertIsEqual(c.XDepth[x], api.Add(xDep.at(c.XParent[x]), 1))
		rng(c.XDepth[x])
	}

	// ---------------- context lookups ----------------
	lCtx, lLvl, lTy := newTable(api, c.LCtx), newTable(api, c.LLvl), newTable(api, c.LTy)
	for l := 0; l < sz.NL; l++ {
		base := c.LBase[l]
		api.AssertIsBoolean(base)
		nb := api.Sub(1, base)
		d := xDep.at(c.LCtx[l])
		dm1 := api.Sub(d, 1)
		eqIf(base, c.LLvl[l], dm1)
		rng(api.Mul(base, dm1))
		eqIf(base, c.LTy[l], xTyp.at(c.LCtx[l]))
		ltIf(nb, c.LNext[l], l)
		eqIf(nb, lCtx.at(c.LNext[l]), xPar.at(c.LCtx[l]))
		eqIf(nb, lLvl.at(c.LNext[l]), c.LLvl[l])
		eqIf(nb, lTy.at(c.LNext[l]), c.LTy[l])
	}

	// ---------------- instantiation ----------------
	iT, iK, iS, iR := newTable(api, c.IT), newTable(api, c.IK), newTable(api, c.IS), newTable(api, c.IR)
	for k := 0; k < sz.NI; k++ {
		t := c.IT[k]
		skip := c.ISkip[k]
		api.AssertIsBoolean(skip)
		live := api.Sub(1, skip)
		tg := tTag.at(t)
		ta, tb, tgG := tA.at(t), tB.at(t), tG.at(t)
		s := onehot(tg, kernel.NumTags)
		api.AssertIsEqual(tG.at(c.IS[k]), 0)
		// skip: BVar K cannot occur, result is T
		geIf(skip, c.IK[k], tgG)
		eqIf(skip, c.IR[k], t)
		// atoms
		atom := api.Mul(live, api.Add(s[kernel.TSort], s[kernel.TFVar], s[kernel.TConst]))
		eqIf(atom, c.IR[k], t)
		isEq := api.IsZero(api.Sub(ta, c.IK[k]))
		eqIf(api.Mul(live, s[kernel.TBVar]), c.IR[k], api.Select(isEq, c.IS[k], t))
		// composites
		comp := api.Mul(live, api.Add(s[kernel.TPi], s[kernel.TLam], s[kernel.TApp]))
		binder := api.Add(s[kernel.TPi], s[kernel.TLam])
		eqIf(comp, tTag.at(c.IR[k]), tg)
		ltIf(comp, c.IC1[k], k)
		ltIf(comp, c.IC2[k], k)
		eqIf(comp, iT.at(c.IC1[k]), ta)
		eqIf(comp, iK.at(c.IC1[k]), c.IK[k])
		eqIf(comp, iS.at(c.IC1[k]), c.IS[k])
		eqIf(comp, iR.at(c.IC1[k]), tA.at(c.IR[k]))
		eqIf(comp, iT.at(c.IC2[k]), tb)
		eqIf(comp, iK.at(c.IC2[k]), api.Add(c.IK[k], binder))
		eqIf(comp, iS.at(c.IC2[k]), c.IS[k])
		eqIf(comp, iR.at(c.IC2[k]), tB.at(c.IR[k]))
	}

	// ---------------- constant table (public) ----------------
	kType, kCtor, kRec, kRhs := newTable(api, c.KType), newTable(api, c.KCtor), newTable(api, c.KRec), newTable(api, c.KRhs)
	kNPre, kNRec, kNCP, kNCA := newTable(api, c.KNPre), newTable(api, c.KNRec), newTable(api, c.KNCP), newTable(api, c.KNCA)

	// ---------------- iota walks ----------------
	wKind, wCtor, wU, wM := newTable(api, c.WKind), newTable(api, c.WCtor), newTable(api, c.WU), newTable(api, c.WM)
	wW, wN := newTable(api, c.WW), newTable(api, c.WN)
	for k := 0; k < sz.NW; k++ {
		s := onehot(c.WKind[k], kernel.NumWKinds)
		j, u, m, w, n, keep := c.WCtor[k], c.WU[k], c.WM[k], c.WW[k], c.WN[k], c.WKeep[k]
		api.AssertIsBoolean(keep)
		nkeep := api.Sub(1, keep)
		rng(n)
		uT, uA, uB := tTag.at(u), tA.at(u), tB.at(u)
		mT, mA, mB := tTag.at(m), tA.at(m), tB.at(m)
		wT, wA, wB := tTag.at(w), tA.at(w), tB.at(w)
		rb, ra, cb, ca := s[kernel.WRecBase], s[kernel.WRecArg], s[kernel.WCtorBase], s[kernel.WCtorArg]
		step := api.Add(ra, cb, ca)
		ltIf(step, c.WPrev[k], k)
		pIdx := api.Mul(step, c.WPrev[k])
		pk, pj, pu, pm, pw, pn := wKind.at(pIdx), wCtor.at(pIdx), wU.at(pIdx), wM.at(pIdx), wW.at(pIdx), wN.at(pIdx)
		nPre, nRec, nCP := kNPre.at(j), kNRec.at(j), kNCP.at(j)
		eqIf(step, pj, j)
		// prev kind ∈ {RecBase, RecArg} resp. {CtorBase, CtorArg}
		recPrev := api.Add(ra, cb)
		api.AssertIsEqual(api.Mul(recPrev, api.Sub(pk, kernel.WRecBase), api.Sub(pk, kernel.WRecArg)), 0)
		api.AssertIsEqual(api.Mul(ca, api.Sub(pk, kernel.WCtorBase), api.Sub(pk, kernel.WCtorArg)), 0)
		// rec base: U = rec, W = Rhs rec
		eqIf(rb, kCtor.at(j), 1)
		eqIf(rb, uT, kernel.TConst)
		eqIf(rb, uA, kRec.at(j))
		eqIf(rb, wT, kernel.TApp)
		eqIf(rb, wA, kRhs.at(j))
		eqIf(rb, wB, u)
		eqIf(api.Add(rb, cb), n, 0)
		// arg steps: N = prev.N + 1; W grows by the argument iff keep
		arg := api.Add(ra, ca)
		eqIf(arg, n, api.Add(pn, 1))
		eqIf(api.Mul(arg, keep), wT, kernel.TApp)
		eqIf(api.Mul(arg, keep), wA, pw)
		eqIf(api.Mul(arg, nkeep), w, pw)
		// rec arg: U = prev.U a, keep ⇔ prev.N < NPre
		eqIf(ra, uT, kernel.TApp)
		eqIf(ra, uA, pu)
		eqIf(api.Mul(ra, keep), wB, uB)
		rng(api.Mul(ra, keep, api.Sub(nPre, pn, 1)))
		rng(api.Mul(ra, nkeep, api.Sub(pn, nPre)))
		// ctor base: prev.N = NRec, M = c, U and W carried
		eqIf(cb, pn, nRec)
		eqIf(cb, mT, kernel.TConst)
		eqIf(cb, mA, j)
		eqIf(cb, w, pw)
		eqIf(api.Add(cb, ca), u, pu)
		// ctor arg: M = prev.M b, keep ⇔ prev.N ≥ NCP
		eqIf(ca, mT, kernel.TApp)
		eqIf(ca, mA, pm)
		eqIf(api.Mul(ca, keep), wB, mB)
		rng(api.Mul(ca, keep, api.Sub(pn, nCP)))
		rng(api.Mul(ca, nkeep, api.Sub(nCP, pn, 1)))
	}

	// ---------------- conversion ----------------
	cT1, cT2 := newTable(api, c.CT1), newTable(api, c.CT2)
	for k := 0; k < sz.NC; k++ {
		s := onehot(c.CRule[k], kernel.NumCRules)
		t1, t2 := c.CT1[k], c.CT2[k]
		api.AssertIsEqual(tG.at(t1), 0)
		api.AssertIsEqual(tG.at(t2), 0)
		g1, a1, b1 := tTag.at(t1), tA.at(t1), tB.at(t1)
		g2, a2, b2 := tTag.at(t2), tA.at(t2), tB.at(t2)
		c1a, c1b := cT1.at(c.CC1[k]), cT2.at(c.CC1[k])
		c2a, c2b := cT1.at(c.CC2[k]), cT2.at(c.CC2[k])
		uses1 := api.Add(s[kernel.CSym], s[kernel.CTrans], s[kernel.CPi], s[kernel.CLam], s[kernel.CApp])
		uses2 := api.Add(s[kernel.CTrans], s[kernel.CPi], s[kernel.CLam], s[kernel.CApp])
		ltIf(uses1, c.CC1[k], k)
		ltIf(uses2, c.CC2[k], k)
		// refl
		eqIf(s[kernel.CRefl], t1, t2)
		// sym
		eqIf(s[kernel.CSym], c1a, t2)
		eqIf(s[kernel.CSym], c1b, t1)
		// trans
		st := s[kernel.CTrans]
		eqIf(st, c1a, t1)
		eqIf(st, c1b, c.CM[k])
		eqIf(st, c2a, c.CM[k])
		eqIf(st, c2b, t2)
		// beta
		sbeta := s[kernel.CBeta]
		fIdx := api.Mul(sbeta, a1)
		eqIf(sbeta, g1, kernel.TApp)
		eqIf(sbeta, tTag.at(fIdx), kernel.TLam)
		i1T, i1K, i1S, i1R := iT.at(c.CI1[k]), iK.at(c.CI1[k]), iS.at(c.CI1[k]), iR.at(c.CI1[k])
		eqIf(sbeta, i1T, tB.at(fIdx))
		eqIf(sbeta, i1K, 0)
		eqIf(sbeta, i1S, b1)
		eqIf(sbeta, i1R, t2)
		// binder congruence
		sb := api.Add(s[kernel.CPi], s[kernel.CLam])
		eqIf(s[kernel.CPi], g1, kernel.TPi)
		eqIf(s[kernel.CPi], g2, kernel.TPi)
		eqIf(s[kernel.CLam], g1, kernel.TLam)
		eqIf(s[kernel.CLam], g2, kernel.TLam)
		eqIf(sb, c1a, a1)
		eqIf(sb, c1b, a2)
		eqIf(sb, tTag.at(c.CV[k]), kernel.TFVar)
		x := tA.at(c.CV[k])
		bIdx1, bIdx2 := api.Mul(sb, b1), api.Mul(sb, b2)
		geIf(sb, x, tF.at(bIdx1))
		geIf(sb, x, tF.at(bIdx2))
		i2T, i2K, i2S, i2R := iT.at(c.CI2[k]), iK.at(c.CI2[k]), iS.at(c.CI2[k]), iR.at(c.CI2[k])
		eqIf(sb, i1T, b1)
		eqIf(sb, i1K, 0)
		eqIf(sb, i1S, c.CV[k])
		eqIf(sb, i2T, b2)
		eqIf(sb, i2K, 0)
		eqIf(sb, i2S, c.CV[k])
		eqIf(sb, c2a, i1R)
		eqIf(sb, c2b, i2R)
		// application congruence
		sa := s[kernel.CApp]
		eqIf(sa, g1, kernel.TApp)
		eqIf(sa, g2, kernel.TApp)
		eqIf(sa, c1a, a1)
		eqIf(sa, c1b, a2)
		eqIf(sa, c2a, b1)
		eqIf(sa, c2b, b2)
		// iota: T1 = App(U, M), T2 = W for a completed walk
		si := s[kernel.CIota]
		wIdx := api.Mul(si, c.CI1[k])
		wk := wKind.at(wIdx)
		api.AssertIsEqual(api.Mul(si, api.Sub(wk, kernel.WCtorBase), api.Sub(wk, kernel.WCtorArg)), 0)
		eqIf(si, wN.at(wIdx), kNCA.at(api.Mul(si, wCtor.at(wIdx))))
		eqIf(si, g1, kernel.TApp)
		eqIf(si, a1, wU.at(wIdx))
		eqIf(si, b1, wM.at(wIdx))
		eqIf(si, t2, wW.at(wIdx))
	}

	// ---------------- judgments ----------------
	jCtx, jSubj, jTy := newTable(api, c.JCtx), newTable(api, c.JSubj), newTable(api, c.JTy)
	for j := 0; j < sz.NJ; j++ {
		s := onehot(c.JRule[j], kernel.NumJRules)
		ctx, subj, ty := c.JCtx[j], c.JSubj[j], c.JTy[j]
		sT, sA, sB, sF := tTag.at(subj), tA.at(subj), tB.at(subj), tF.at(subj)
		yT, yA, yB, yF := tTag.at(ty), tA.at(ty), tB.at(ty), tF.at(ty)
		api.AssertIsEqual(tG.at(subj), 0)
		api.AssertIsEqual(tG.at(ty), 0)
		d := xDep.at(ctx)
		geIf(1, d, sF)
		geIf(1, d, yF)

		uses := api.Add(s[kernel.JPi], s[kernel.JLam], s[kernel.JApp], s[kernel.JConv])
		ltIf(uses, c.JC1[j], j)
		ltIf(uses, c.JC2[j], j)
		c1ctx, c1s, c1y := jCtx.at(c.JC1[j]), jSubj.at(c.JC1[j]), jTy.at(c.JC1[j])
		c2ctx, c2s, c2y := jCtx.at(c.JC2[j]), jSubj.at(c.JC2[j]), jTy.at(c.JC2[j])
		y1T, y1A, y1B := tTag.at(c1y), tA.at(c1y), tB.at(c1y)
		y2T, y2A := tTag.at(c2y), tA.at(c2y)
		i1T, i1K, i1S, i1R := iT.at(c.JI1[j]), iK.at(c.JI1[j]), iS.at(c.JI1[j]), iR.at(c.JI1[j])
		i2T, i2K, i2S, i2R := iT.at(c.JI2[j]), iK.at(c.JI2[j]), iS.at(c.JI2[j]), iR.at(c.JI2[j])

		// Sort
		ss := s[kernel.JSort]
		eqIf(ss, sT, kernel.TSort)
		eqIf(ss, yT, kernel.TSort)
		eqIf(ss, yA, api.Add(sA, 1))
		// Var
		sv := s[kernel.JVar]
		eqIf(sv, sT, kernel.TFVar)
		eqIf(sv, lCtx.at(c.JL[j]), ctx)
		eqIf(sv, lLvl.at(c.JL[j]), sA)
		eqIf(sv, lTy.at(c.JL[j]), ty)
		// Pi / Lam common: open the body with the fresh variable FVar(depth)
		sp, sl := s[kernel.JPi], s[kernel.JLam]
		sb := api.Add(sp, sl)
		eqIf(sb, xPar.at(c.JX[j]), ctx)
		eqIf(sb, xTyp.at(c.JX[j]), sA)
		eqIf(sb, tTag.at(c.JV[j]), kernel.TFVar)
		eqIf(sb, tA.at(c.JV[j]), d)
		eqIf(sb, i1T, sB)
		eqIf(sb, i1K, 0)
		eqIf(sb, i1S, c.JV[j])
		eqIf(sb, c2ctx, c.JX[j])
		eqIf(sb, c2s, i1R)
		eqIf(sb, c1ctx, ctx)
		// Pi
		eqIf(sp, sT, kernel.TPi)
		eqIf(sp, c1s, sA)
		eqIf(sp, y1T, kernel.TSort)
		eqIf(sp, y2T, kernel.TSort)
		m := c.JM[j]
		geIf(sp, m, y1A)
		geIf(sp, m, y2A)
		api.AssertIsEqual(api.Mul(sp, api.Sub(m, y1A), api.Sub(m, y2A)), 0)
		wZero := api.IsZero(y2A)
		eqIf(sp, yT, kernel.TSort)
		eqIf(sp, yA, api.Mul(api.Sub(1, wZero), m))
		// Lam
		eqIf(sl, sT, kernel.TLam)
		eqIf(sl, yT, kernel.TPi)
		eqIf(sl, yA, sA)
		eqIf(sl, c1s, ty)
		eqIf(sl, y1T, kernel.TSort)
		eqIf(sl, i2T, yB)
		eqIf(sl, i2K, 0)
		eqIf(sl, i2S, c.JV[j])
		eqIf(sl, c2y, i2R)
		// App
		sa := s[kernel.JApp]
		eqIf(sa, sT, kernel.TApp)
		eqIf(sa, c1ctx, ctx)
		eqIf(sa, c1s, sA)
		eqIf(sa, y1T, kernel.TPi)
		eqIf(sa, c2ctx, ctx)
		eqIf(sa, c2s, sB)
		eqIf(sa, c2y, y1A)
		eqIf(sa, i1T, y1B)
		eqIf(sa, i1K, 0)
		eqIf(sa, i1S, sB)
		eqIf(sa, i1R, ty)
		// Conv
		sc := s[kernel.JConv]
		eqIf(sc, c1ctx, ctx)
		eqIf(sc, c1s, subj)
		eqIf(sc, cT1.at(c.JCv[j]), c1y)
		eqIf(sc, cT2.at(c.JCv[j]), ty)
		eqIf(sc, c2ctx, ctx)
		eqIf(sc, c2s, ty)
		eqIf(sc, y2T, kernel.TSort)
		// Const: c.{u} : Type(c)[BVar 0 := Sort u]
		sk := s[kernel.JConst]
		eqIf(sk, sT, kernel.TConst)
		eqIf(sk, tTag.at(c.JV[j]), kernel.TSort)
		eqIf(sk, tA.at(c.JV[j]), sB)
		eqIf(sk, i1T, kType.at(api.Mul(sk, sA)))
		eqIf(sk, i1K, 0)
		eqIf(sk, i1S, c.JV[j])
		eqIf(sk, i1R, ty)
	}

	// ---------------- root ----------------
	api.AssertIsEqual(c.JCtx[sz.NJ-1], 0)
	api.AssertIsEqual(c.JTy[sz.NJ-1], c.Root)
	return nil
}

// Assign builds a full witness assignment from a padded certificate.
func Assign(cert *kernel.Certificate, sz kernel.Sizes) *Circuit {
	c := New(sz)
	PublicAssign(c, cert.S, cert.Root, sz)
	n := cert.S.Nodes
	for i := sz.NP; i < sz.NT; i++ {
		c.Tag[i-sz.NP], c.A[i-sz.NP], c.B[i-sz.NP] = n[i].Tag, n[i].A, n[i].B
	}
	for i := 0; i < sz.NT; i++ {
		c.F[i], c.G[i] = n[i].F, n[i].G
	}
	for i, r := range cert.Ctx {
		c.XParent[i], c.XType[i], c.XDepth[i] = r.Parent, r.Type, r.Depth
	}
	for i, r := range cert.Look {
		c.LCtx[i], c.LLvl[i], c.LTy[i], c.LBase[i], c.LNext[i] = r.Ctx, r.Lvl, r.Ty, r.Base, r.Next
	}
	for i, r := range cert.Inst {
		c.IT[i], c.IK[i], c.IS[i], c.IR[i], c.IC1[i], c.IC2[i], c.ISkip[i] = r.T, r.K, r.S, r.R, r.C1, r.C2, r.Skip
	}
	for i, r := range cert.Conv {
		c.CRule[i], c.CT1[i], c.CT2[i], c.CC1[i], c.CC2[i], c.CI1[i], c.CI2[i], c.CV[i], c.CM[i] =
			r.Rule, r.T1, r.T2, r.C1, r.C2, r.I1, r.I2, r.V, r.M
	}
	for i, r := range cert.Jud {
		c.JRule[i], c.JCtx[i], c.JSubj[i], c.JTy[i], c.JC1[i], c.JC2[i] = r.Rule, r.Ctx, r.Subj, r.Ty, r.C1, r.C2
		c.JI1[i], c.JI2[i], c.JX[i], c.JV[i], c.JL[i], c.JCv[i], c.JM[i] = r.I1, r.I2, r.X, r.V, r.L, r.Cv, r.M
	}
	for i, r := range cert.Iota {
		c.WKind[i], c.WCtor[i], c.WU[i], c.WM[i], c.WW[i], c.WN[i], c.WPrev[i], c.WKeep[i] =
			r.Kind, r.Ctor, r.U, r.M, r.W, r.N, r.Prev, r.Keep
	}
	return c
}

// PublicAssign fills only the public inputs (what the verifier computes).
func PublicAssign(c *Circuit, s *kernel.Store, root int, sz kernel.Sizes) {
	for i := 0; i < sz.NP; i++ {
		n := s.Nodes[i]
		c.PubTag[i], c.PubA[i], c.PubB[i] = n.Tag, n.A, n.B
	}
	c.Root = root
	for i := 0; i < sz.NK; i++ {
		var k kernel.ConstRow
		if i < len(s.Consts) {
			k = s.Consts[i]
		}
		c.KType[i], c.KCtor[i], c.KRec[i], c.KRhs[i] = k.Type, k.Ctor, k.Rec, k.Rhs
		c.KNPre[i], c.KNRec[i], c.KNCP[i], c.KNCA[i] = k.NPre, k.NRec, k.NCP, k.NCA
	}
}
