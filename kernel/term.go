// Package kernel implements the trusted core of zkLean: a locally-nameless
// Calculus of Constructions with a predicative-over-impredicative universe
// hierarchy Sort 0 (= Prop) : Sort 1 (= Type) : Sort 2 : ...  — the same
// universe structure as Lean 4's kernel, minus universe polymorphism,
// inductive types and definitional unfolding (definitions are expanded at
// elaboration time).
//
// Terms are hash-consed into a DAG (Store). Every node has a numeric id, and
// all children have strictly smaller ids. This is exactly the "term table"
// that is committed inside the zero-knowledge circuit.
package kernel

import (
	"fmt"
	"strings"
)

// Term tags. These numeric values are part of the circuit's relation.
const (
	TSort = 0 // A = universe level
	TBVar = 1 // A = de Bruijn index (bound variable, only inside binders)
	TFVar = 2 // A = de Bruijn *level* of a context entry (free variable)
	TPi   = 3 // A = domain, B = body (body binds BVar 0)
	TLam  = 4 // A = domain, B = body
	TApp  = 5 // A = function, B = argument
)

var tagNames = []string{"Sort", "BVar", "FVar", "Pi", "Lam", "App"}

// Node is one row of the term table.
//
//	F = an upper bound on 1 + (largest free-variable level occurring), 0 if none
//	G = an upper bound on 1 + (largest loose bound-variable index), 0 if locally closed
//
// The store always records the exact values; the circuit only enforces that
// they are upper bounds, which is all soundness needs.
type Node struct {
	Tag, A, B int
	F, G      int
}

func IsComposite(tag int) bool { return tag == TPi || tag == TLam || tag == TApp }

// Store is a hash-consed term DAG.
type Store struct {
	Nodes []Node
	idx   map[[3]int]int
	// memo tables for pure operations
	instMemo  map[[3]int]int
	closeMemo map[[3]int]int
}

func NewStore() *Store {
	return &Store{
		idx:       map[[3]int]int{},
		instMemo:  map[[3]int]int{},
		closeMemo: map[[3]int]int{},
	}
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

// Mk returns the id of the node (tag, a, b), creating it if necessary.
func (s *Store) Mk(tag, a, b int) int {
	if !IsComposite(tag) {
		b = 0
	}
	k := [3]int{tag, a, b}
	if id, ok := s.idx[k]; ok {
		return id
	}
	n := Node{Tag: tag, A: a, B: b}
	switch tag {
	case TSort:
	case TBVar:
		n.G = a + 1
	case TFVar:
		n.F = a + 1
	case TPi, TLam:
		n.F = max(s.Nodes[a].F, s.Nodes[b].F)
		n.G = max(s.Nodes[a].G, max(s.Nodes[b].G-1, 0))
	case TApp:
		n.F = max(s.Nodes[a].F, s.Nodes[b].F)
		n.G = max(s.Nodes[a].G, s.Nodes[b].G)
	default:
		panic("bad tag")
	}
	s.Nodes = append(s.Nodes, n)
	id := len(s.Nodes) - 1
	s.idx[k] = id
	return id
}

// AppendRaw appends a node without hash-consing (used for padding rows).
func (s *Store) AppendRaw(n Node) int {
	s.Nodes = append(s.Nodes, n)
	return len(s.Nodes) - 1
}

func (s *Store) N(id int) Node { return s.Nodes[id] }

func (s *Store) Sort(u int) int   { return s.Mk(TSort, u, 0) }
func (s *Store) BVar(i int) int   { return s.Mk(TBVar, i, 0) }
func (s *Store) FVar(l int) int   { return s.Mk(TFVar, l, 0) }
func (s *Store) Pi(a, b int) int  { return s.Mk(TPi, a, b) }
func (s *Store) Lam(a, b int) int { return s.Mk(TLam, a, b) }
func (s *Store) App(f, a int) int { return s.Mk(TApp, f, a) }
func (s *Store) Apps(f int, as ...int) int {
	for _, a := range as {
		f = s.App(f, a)
	}
	return f
}

// Inst replaces BVar k by the locally-closed term v (no shifting is needed
// because v has no loose bound variables).
func (s *Store) Inst(t, k, v int) int {
	key := [3]int{t, k, v}
	if r, ok := s.instMemo[key]; ok {
		return r
	}
	n := s.Nodes[t]
	var r int
	switch n.Tag {
	case TSort, TFVar:
		r = t
	case TBVar:
		if n.A == k {
			r = v
		} else {
			r = t
		}
	case TPi, TLam:
		r = s.Mk(n.Tag, s.Inst(n.A, k, v), s.Inst(n.B, k+1, v))
	case TApp:
		r = s.Mk(n.Tag, s.Inst(n.A, k, v), s.Inst(n.B, k, v))
	}
	s.instMemo[key] = r
	return r
}

// Close replaces FVar lvl by BVar k (the inverse of Inst with an FVar).
func (s *Store) Close(t, lvl, k int) int {
	if s.Nodes[t].F <= lvl {
		return t
	}
	key := [3]int{t, lvl, k}
	if r, ok := s.closeMemo[key]; ok {
		return r
	}
	n := s.Nodes[t]
	var r int
	switch n.Tag {
	case TSort, TBVar:
		r = t
	case TFVar:
		if n.A == lvl {
			r = s.BVar(k)
		} else {
			r = t
		}
	case TPi, TLam:
		r = s.Mk(n.Tag, s.Close(n.A, lvl, k), s.Close(n.B, lvl, k+1))
	case TApp:
		r = s.Mk(n.Tag, s.Close(n.A, lvl, k), s.Close(n.B, lvl, k))
	}
	s.closeMemo[key] = r
	return r
}

// Import copies term id from src into s (post-order, deterministic), returning
// the new id. Used to lay out the public statement canonically.
func (s *Store) Import(src *Store, id int, memo map[int]int) int {
	if r, ok := memo[id]; ok {
		return r
	}
	n := src.Nodes[id]
	var r int
	if IsComposite(n.Tag) {
		a := s.Import(src, n.A, memo)
		b := s.Import(src, n.B, memo)
		r = s.Mk(n.Tag, a, b)
	} else {
		r = s.Mk(n.Tag, n.A, 0)
	}
	memo[id] = r
	return r
}

// Size returns the number of distinct DAG nodes reachable from id.
func (s *Store) Size(id int) int {
	seen := map[int]bool{}
	var go_ func(int)
	go_ = func(i int) {
		if seen[i] {
			return
		}
		seen[i] = true
		n := s.Nodes[i]
		if IsComposite(n.Tag) {
			go_(n.A)
			go_(n.B)
		}
	}
	go_(id)
	return len(seen)
}

// Show pretty-prints a term (bound variables are named x0, x1, ... by depth).
func (s *Store) Show(id int) string {
	var b strings.Builder
	s.show(&b, id, 0, 0)
	return b.String()
}

func (s *Store) show(b *strings.Builder, id, depth, prec int) {
	n := s.Nodes[id]
	paren := func(p int, f func()) {
		if prec > p {
			b.WriteString("(")
			f()
			b.WriteString(")")
		} else {
			f()
		}
	}
	switch n.Tag {
	case TSort:
		switch n.A {
		case 0:
			b.WriteString("Prop")
		case 1:
			b.WriteString("Type")
		default:
			fmt.Fprintf(b, "Sort %d", n.A)
		}
	case TBVar:
		if n.A < depth {
			fmt.Fprintf(b, "x%d", depth-1-n.A)
		} else {
			fmt.Fprintf(b, "#%d", n.A)
		}
	case TFVar:
		fmt.Fprintf(b, "f%d", n.A)
	case TPi:
		paren(0, func() {
			if s.Nodes[n.B].G == 0 || !s.usesBVar0(n.B) {
				s.show(b, n.A, depth, 1)
				b.WriteString(" → ")
				s.show(b, n.B, depth+1, 0)
			} else {
				fmt.Fprintf(b, "∀ (x%d : ", depth)
				s.show(b, n.A, depth, 0)
				b.WriteString("), ")
				s.show(b, n.B, depth+1, 0)
			}
		})
	case TLam:
		paren(0, func() {
			fmt.Fprintf(b, "fun (x%d : ", depth)
			s.show(b, n.A, depth, 0)
			b.WriteString(") => ")
			s.show(b, n.B, depth+1, 0)
		})
	case TApp:
		paren(1, func() {
			s.show(b, n.A, depth, 1)
			b.WriteString(" ")
			s.show(b, n.B, depth, 2)
		})
	}
}

// usesBVar0 reports whether BVar 0 (relative to t) occurs in t.
func (s *Store) usesBVar0(t int) bool {
	var occ func(t, k int) bool
	memo := map[[2]int]bool{}
	occ = func(t, k int) bool {
		n := s.Nodes[t]
		if n.G <= k {
			return false
		}
		key := [2]int{t, k}
		if v, ok := memo[key]; ok {
			return v
		}
		var r bool
		switch n.Tag {
		case TBVar:
			r = n.A == k
		case TPi, TLam:
			r = occ(n.A, k) || occ(n.B, k+1)
		case TApp:
			r = occ(n.A, k) || occ(n.B, k)
		}
		memo[key] = r
		return r
	}
	return occ(t, 0)
}
