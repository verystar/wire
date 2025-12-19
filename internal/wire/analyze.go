// Copyright 2018 The Wire Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package wire

import (
	"errors"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strings"

	"golang.org/x/tools/go/types/typeutil"
)

type callKind int

const (
	funcProviderCall callKind = iota
	structProvider
	valueExpr
	selectorExpr
)

// A call represents a step of an injector function.  It may be either a
// function call or a composite struct literal, depending on the value
// of kind.
type call struct {
	// kind indicates the code pattern to use.
	kind callKind

	// out is the type this step produces.
	out types.Type

	// pkg and name identify one of the following:
	// 1) the provider to call for kind == funcProviderCall;
	// 2) the type to construct for kind == structProvider;
	// 3) the name to select for kind == selectorExpr.
	pkg  *types.Package
	name string

	// args is a list of arguments to call the provider with. Each element is:
	// a) one of the givens (args[i] < len(given)),
	// b) the result of a previous provider call (args[i] >= len(given))
	//
	// This will be nil for kind == valueExpr.
	//
	// If kind == selectorExpr, then the length of this slice will be 1 and the
	// "argument" will be the value to access fields from.
	args []int

	// varargs is true if the provider function is variadic.
	varargs bool

	// fieldNames maps the arguments to struct field names.
	// This will only be set if kind == structProvider.
	fieldNames []string

	// ins is the list of types this call receives as arguments.
	// This will be nil for kind == valueExpr.
	ins []types.Type

	// The following are only set for kind == funcProviderCall:

	// hasCleanup is true if the provider call returns a cleanup function.
	hasCleanup bool
	// hasErr is true if the provider call returns an error.
	hasErr bool

	// The following are only set for kind == valueExpr:

	valueExpr     ast.Expr
	valueTypeInfo *types.Info

	// The following are only set for kind == selectorExpr:

	ptrToField bool
}

func sameProvider(a, b ProvidedType) bool {
	if a.IsProvider() && b.IsProvider() {
		return a.Provider() == b.Provider()
	}
	if a.IsValue() && b.IsValue() {
		return a.Value() == b.Value()
	}
	if a.IsField() && b.IsField() {
		return a.Field() == b.Field()
	}
	if a.IsArg() && b.IsArg() {
		return a.Arg().Index == b.Arg().Index
	}
	return false
}

// solve finds the sequence of calls required to produce an output type
// with an optional set of provided inputs.
func solve(fset *token.FileSet, out types.Type, given *types.Tuple, set *ProviderSet) ([]call, []error) {
	ec := new(errorCollector)

	// Start building the mapping of type to local variable of the given type.
	// The first len(given) local variables are the given types.
	index := new(typeutil.Map)
	index.SetHasher(typeutil.MakeHasher())
	// indexByDecl maps a concrete type to a map of declared type qualified name to local variable index.
	indexByDecl := new(typeutil.Map)
	indexByDecl.SetHasher(typeutil.MakeHasher())
	for i := 0; i < given.Len(); i++ {
		index.Set(given.At(i).Type(), i)
	}

	// Topological sort of the directed graph defined by the providers
	// using a depth-first search using a stack. Provider set graphs are
	// guaranteed to be acyclic. An index value of errAbort indicates that
	// the type was visited, but failed due to an error added to ec.
	errAbort := errors.New("failed to visit")
	var used []*providerSetSrc
	var calls []call
	type frame struct {
		t        types.Type
		from     types.Type
		up       *frame
		declName string
	}
	stk := []frame{{t: out}}

	updateIndex := func(t types.Type, declName string, pt ProvidedType) {
		valIndex := given.Len() + len(calls)

		setIndex := func(dn string) {
			if dn != "" {
				m := indexByDecl.At(t)
				var mp map[string]int
				if m == nil {
					mp = make(map[string]int)
					indexByDecl.Set(t, mp)
				} else {
					mp = m.(map[string]int)
				}
				if _, ok := mp[dn]; !ok {
					mp[dn] = valIndex
				}
			} else {
				if index.At(t) == nil {
					index.Set(t, valIndex)
				}
			}
		}

		setIndex(declName)

		// Aliases
		if defaultPt := set.providerMap.At(t); defaultPt != nil {
			dpt := defaultPt.(*ProvidedType)
			if sameProvider(pt, *dpt) {
				setIndex("")
			}
		}
		if set.declProviderMap != nil {
			if m := set.declProviderMap.At(t); m != nil {
				mp := m.(map[string]*ProvidedType)
				for dn, dpt := range mp {
					if sameProvider(pt, *dpt) {
						setIndex(dn)
					}
				}
			}
		}
	}

dfs:
	for len(stk) > 0 {
		curr := stk[len(stk)-1]
		stk = stk[:len(stk)-1]

		// Check visited by declared name if applicable.
		if curr.declName != "" {
			if m := indexByDecl.At(curr.t); m != nil {
				if _, ok := m.(map[string]int)[curr.declName]; ok {
					continue
				}
			}
		} else if index.At(curr.t) != nil {
			continue
		}

		pv := set.forWithDeclName(curr.t, curr.declName)
		if pv.IsNil() {
			if curr.from == nil {
				ec.add(fmt.Errorf("no provider found for %s, output of injector", types.TypeString(curr.t, nil)))
				index.Set(curr.t, errAbort)
				continue
			}
			sb := new(strings.Builder)
			fmt.Fprintf(sb, "no provider found for %s", types.TypeString(curr.t, nil))
			for f := curr.up; f != nil; f = f.up {
				fmt.Fprintf(sb, "\nneeded by %s in %s", types.TypeString(f.t, nil), set.srcMap.At(f.t).(*providerSetSrc).description(fset, f.t))
			}
			ec.add(errors.New(sb.String()))
			index.Set(curr.t, errAbort)
			continue
		}
		src := set.srcMap.At(curr.t).(*providerSetSrc)
		if curr.declName != "" && set.declSrcMap != nil {
			if m := set.declSrcMap.At(curr.t); m != nil {
				if s := m.(map[string]*providerSetSrc)[curr.declName]; s != nil {
					src = s
				}
			}
		}
		used = append(used, src)
		if concrete := pv.Type(); !types.Identical(concrete, curr.t) {
			// Interface binding does not create a call.
			i := index.At(concrete)
			if i == nil {
				stk = append(stk, curr, frame{t: concrete, from: curr.t, up: &curr})
				continue
			}
			index.Set(curr.t, i)
			continue
		}

		switch pv := set.forWithDeclName(curr.t, curr.declName); {
		case pv.IsArg():
			if curr.declName != "" {
				if v := index.At(curr.t); v != nil {
					m := indexByDecl.At(curr.t)
					var mp map[string]int
					if m == nil {
						mp = make(map[string]int)
						indexByDecl.Set(curr.t, mp)
					} else {
						mp = m.(map[string]int)
					}
					mp[curr.declName] = v.(int)
				}
			}
			// Continue, already added to stk.
		case pv.IsProvider():
			p := pv.Provider()
			// Ensure that all argument types have been visited. If not, push them
			// on the stack in reverse order so that calls are added in argument
			// order.
			visitedArgs := true
			for i := len(p.Args) - 1; i >= 0; i-- {
				a := p.Args[i]
				var visited bool
				if a.Decl != nil {
					if m := indexByDecl.At(a.Type); m != nil {
						var key string
						if a.Decl.Pkg() != nil {
							key = a.Decl.Pkg().Path() + "." + a.Decl.Name()
						} else {
							key = a.Decl.Name()
						}
						_, visited = m.(map[string]int)[key]
					}
				} else {
					visited = index.At(a.Type) != nil
				}
				if !visited {
					if visitedArgs {
						// Make sure to re-visit this type after visiting all arguments.
						stk = append(stk, curr)
						visitedArgs = false
					}
				var dn string
					if a.Decl != nil {
						if a.Decl.Pkg() != nil {
							dn = a.Decl.Pkg().Path() + "." + a.Decl.Name()
						} else {
							dn = a.Decl.Name()
						}
					}
					stk = append(stk, frame{t: a.Type, from: curr.t, up: &curr, declName: dn})
				}
			}
			if !visitedArgs {
				continue
			}
			args := make([]int, len(p.Args))
			ins := make([]types.Type, len(p.Args))
			for i := range p.Args {
				ins[i] = p.Args[i].Type
				var v interface{}
				if p.Args[i].Decl != nil {
					if m := indexByDecl.At(p.Args[i].Type); m != nil {
						var key string
						if p.Args[i].Decl.Pkg() != nil {
							key = p.Args[i].Decl.Pkg().Path() + "." + p.Args[i].Decl.Name()
						} else {
							key = p.Args[i].Decl.Name()
						}
						v = m.(map[string]int)[key]
					}
				}
				if v == nil {
					v = index.At(p.Args[i].Type)
				}
				if v == errAbort {
					index.Set(curr.t, errAbort)
					continue dfs
				}
				args[i] = v.(int)
			}
			// Assign local variable index for produced type considering declaration name.
			updateIndex(curr.t, curr.declName, pv)
			kind := funcProviderCall
			fieldNames := []string(nil)
			if p.IsStruct {
				kind = structProvider
				for _, arg := range p.Args {
					fieldNames = append(fieldNames, arg.FieldName)
				}
			}
			calls = append(calls, call{
				kind:       kind,
				pkg:        p.Pkg,
				name:       p.Name,
				args:       args,
				varargs:    p.Varargs,
				fieldNames: fieldNames,
				ins:        ins,
				out:        curr.t,
				hasCleanup: p.HasCleanup,
				hasErr:     p.HasErr,
			})
		case pv.IsValue():
			v := pv.Value()
			updateIndex(curr.t, curr.declName, pv)
			calls = append(calls, call{
				kind:          valueExpr,
				out:           curr.t,
				valueExpr:     v.expr,
				valueTypeInfo: v.info,
			})
		case pv.IsField():
			f := pv.Field()
			if index.At(f.Parent) == nil {
				// Fields have one dependency which is the parent struct. Make
				// sure to visit it first if it is not already visited.
				stk = append(stk, curr, frame{t: f.Parent, from: curr.t, up: &curr})
				continue
			}
			updateIndex(curr.t, curr.declName, pv)
			v := index.At(f.Parent)
			if v == errAbort {
				index.Set(curr.t, errAbort)
				continue dfs
			}
			// Use args[0] to store the position of the parent struct.
			args := []int{v.(int)}
			// If f.Out has 2 elements and curr.t is the 2nd one, then the call must
			// provide a pointer to the field.
			ptrToField := len(f.Out) == 2 && types.Identical(curr.t, f.Out[1])
			calls = append(calls, call{
				kind:       selectorExpr,
				pkg:        f.Pkg,
				name:       f.Name,
				out:        curr.t,
				args:       args,
				ptrToField: ptrToField,
			})
		default:
			panic("unknown return value from ProviderSet.For")
		}
	}
	if len(ec.errors) > 0 {
		return nil, ec.errors
	}
	if errs := verifyArgsUsed(set, used); len(errs) > 0 {
		return nil, errs
	}
	return calls, nil
}

// verifyArgsUsed ensures that all of the arguments in set were used during solve.
func verifyArgsUsed(set *ProviderSet, used []*providerSetSrc) []error {
	var errs []error
	for _, imp := range set.Imports {
		found := false
		for _, u := range used {
			if u.Import == imp {
				found = true
				break
			}
		}
		if !found {
			if imp.VarName == "" {
				errs = append(errs, errors.New("unused provider set"))
			} else {
				errs = append(errs, fmt.Errorf("unused provider set %q", imp.VarName))
			}
		}
	}
	for _, p := range set.Providers {
		found := false
		for _, u := range used {
			if u.Provider == p {
				found = true
				break
			}
		}
		if !found {
			errs = append(errs, fmt.Errorf("unused provider %q", p.Pkg.Name()+"."+p.Name))
		}
	}
	for _, v := range set.Values {
		found := false
		for _, u := range used {
			if u.Value == v {
				found = true
				break
			}
		}
		if !found {
			errs = append(errs, fmt.Errorf("unused value of type %s", types.TypeString(v.Out, nil)))
		}
	}
	for _, b := range set.Bindings {
		found := false
		for _, u := range used {
			if u.Binding == b {
				found = true
				break
			}
		}
		if !found {
			errs = append(errs, fmt.Errorf("unused interface binding to type %s", types.TypeString(b.Iface, nil)))
		}
	}
	for _, f := range set.Fields {
		found := false
		for _, u := range used {
			if u.Field == f {
				found = true
				break
			}
		}
		if !found {
			errs = append(errs, fmt.Errorf("unused field %q.%s", f.Parent, f.Name))
		}
	}
	return errs
}

// buildProviderMap creates the providerMap and srcMap fields for a given
// provider set. The given provider set's providerMap and srcMap fields are
// ignored.
func buildProviderMap(fset *token.FileSet, hasher typeutil.Hasher, set *ProviderSet) (*typeutil.Map, *typeutil.Map, []error) {
	providerMap := new(typeutil.Map)
	providerMap.SetHasher(hasher)
	srcMap := new(typeutil.Map) // to *providerSetSrc
	srcMap.SetHasher(hasher)

	ec := new(errorCollector)
	// Process injector arguments.
	if set.InjectorArgs != nil {
		givens := set.InjectorArgs.Tuple
		for i := 0; i < givens.Len(); i++ {
			typ := givens.At(i).Type()
			arg := &InjectorArg{Args: set.InjectorArgs, Index: i}
			src := &providerSetSrc{InjectorArg: arg}
			if prevSrc := srcMap.At(typ); prevSrc != nil {
				ec.add(bindingConflictError(fset, typ, set, src, prevSrc.(*providerSetSrc)))
				continue
			}
			providerMap.Set(typ, &ProvidedType{t: typ, a: arg})
			srcMap.Set(typ, src)
		}
	}
	// Process imports, verifying that there are no conflicts between sets.
	for _, imp := range set.Imports {
		src := &providerSetSrc{Import: imp}
		imp.providerMap.Iterate(func(k types.Type, v interface{}) {
			if prevSrc := srcMap.At(k); prevSrc != nil {
				ec.add(bindingConflictError(fset, k, set, src, prevSrc.(*providerSetSrc)))
				return
			}
			providerMap.Set(k, v)
			srcMap.Set(k, src)
		})
	}
	if len(ec.errors) > 0 {
		return nil, nil, ec.errors
	}

	// Process non-binding providers in new set.
	for _, p := range set.Providers {
		src := &providerSetSrc{Provider: p}
		for _, typ := range p.Out {
			if prevSrc := srcMap.At(typ); prevSrc != nil {
				// Allow multiple providers for the same concrete type when they differ
				// by declared output type name; record in declProviderMap for selection.
				if set.declProviderMap != nil {
					m := set.declProviderMap.At(typ)
				var mp map[string]*ProvidedType
				var ms map[string]*providerSetSrc
				ms_iface := set.declSrcMap.At(typ)
				if ms_iface == nil {
					ms = make(map[string]*providerSetSrc)
					set.declSrcMap.Set(typ, ms)
				} else {
					ms = ms_iface.(map[string]*providerSetSrc)
				}

				if m == nil {
					mp = make(map[string]*ProvidedType)
					set.declProviderMap.Set(typ, mp)
					// Seed with previous provider if it has a declared name.
					prev := prevSrc.(*providerSetSrc)
					if prev.Provider != nil && len(prev.Provider.OutNamedObjs) > 0 {
						q := prev.Provider.OutNamedObjs[0]
						if q != nil {
							var key string
							if q.Pkg() != nil {
								key = q.Pkg().Path() + "." + q.Name()
							} else {
								key = q.Name()
							}
							if _, ok := mp[key]; !ok {
								mp[key] = &ProvidedType{t: typ, p: prev.Provider}
								ms[key] = prev
							}
						}
					}
				} else {
					mp = m.(map[string]*ProvidedType)
				}
				if len(p.OutNamedObjs) > 0 {
					q := p.OutNamedObjs[0]
					if q != nil {
						var key string
						if q.Pkg() != nil {
							key = q.Pkg().Path() + "." + q.Name()
						} else {
							key = q.Name()
						}
						mp[key] = &ProvidedType{t: typ, p: p}
						ms[key] = src
					}
					// Do not treat as conflict error; keep existing providerMap/srcMap entries.
					continue
				}
				}
				// If no declared name available, treat as conflict.
				ec.add(bindingConflictError(fset, typ, set, src, prevSrc.(*providerSetSrc)))
				continue
			}
			providerMap.Set(typ, &ProvidedType{t: typ, p: p})
			srcMap.Set(typ, src)
			// Record declared output for selection.
			if len(p.OutNamedObjs) > 0 && set.declProviderMap != nil {
				m := set.declProviderMap.At(typ)
				var mp map[string]*ProvidedType
				var ms map[string]*providerSetSrc
				ms_iface := set.declSrcMap.At(typ)
				if ms_iface == nil {
					ms = make(map[string]*providerSetSrc)
					set.declSrcMap.Set(typ, ms)
				} else {
					ms = ms_iface.(map[string]*providerSetSrc)
				}

				if m == nil {
					mp = make(map[string]*ProvidedType)
					set.declProviderMap.Set(typ, mp)
				} else {
					mp = m.(map[string]*ProvidedType)
				}
				q := p.OutNamedObjs[0]
				if q != nil {
					var key string
					if q.Pkg() != nil {
						key = q.Pkg().Path() + "." + q.Name()
					} else {
						key = q.Name()
					}
					mp[key] = &ProvidedType{t: typ, p: p}
					ms[key] = src
				}
			}
		}
	}
	for _, v := range set.Values {
		src := &providerSetSrc{Value: v}
		if prevSrc := srcMap.At(v.Out); prevSrc != nil {
			ec.add(bindingConflictError(fset, v.Out, set, src, prevSrc.(*providerSetSrc)))
			continue
		}
		providerMap.Set(v.Out, &ProvidedType{t: v.Out, v: v})
		srcMap.Set(v.Out, src)
	}
	for _, f := range set.Fields {
		src := &providerSetSrc{Field: f}
		for _, typ := range f.Out {
			if prevSrc := srcMap.At(typ); prevSrc != nil {
				ec.add(bindingConflictError(fset, typ, set, src, prevSrc.(*providerSetSrc)))
				continue
			}
			providerMap.Set(typ, &ProvidedType{t: typ, f: f})
			srcMap.Set(typ, src)
		}
	}
	if len(ec.errors) > 0 {
		return nil, nil, ec.errors
	}

	// Process bindings in set. Must happen after the other providers to
	// ensure the concrete type is being provided.
	for _, b := range set.Bindings {
		src := &providerSetSrc{Binding: b}
		if prevSrc := srcMap.At(b.Iface); prevSrc != nil {
			ec.add(bindingConflictError(fset, b.Iface, set, src, prevSrc.(*providerSetSrc)))
			continue
		}
		concrete := providerMap.At(b.Provided)
		if concrete == nil {
			setName := set.VarName
			if setName == "" {
				setName = "provider set"
			}
			ec.add(notePosition(fset.Position(b.Pos), fmt.Errorf("wire.Bind of concrete type %q to interface %q, but %s does not include a provider for %q", b.Provided, b.Iface, setName, b.Provided)))
			continue
		}
		providerMap.Set(b.Iface, concrete)
		srcMap.Set(b.Iface, src)
	}
	if len(ec.errors) > 0 {
		return nil, nil, ec.errors
	}
	return providerMap, srcMap, nil
}

func verifyAcyclic(set *ProviderSet, hasher typeutil.Hasher) []error {
	// We must visit every provider type inside provider map, but we don't
	// have a well-defined starting point and there may be several
	// distinct graphs. Thus, we start a depth-first search at every
	// provider, but keep a shared record of visited providers to avoid
	// duplicating work.
	visited := new(typeutil.Map) // to map[string]bool (declName -> visited)
	visited.SetHasher(hasher)
	ec := new(errorCollector)

	type graphNode struct {
		t        types.Type
		declName string
	}

	// Collect all roots
	var roots []graphNode
	set.providerMap.Iterate(func(t types.Type, v interface{}) {
		roots = append(roots, graphNode{t: t, declName: ""})
	})
	if set.declProviderMap != nil {
		set.declProviderMap.Iterate(func(t types.Type, v interface{}) {
			m := v.(map[string]*ProvidedType)
			for dn := range m {
				roots = append(roots, graphNode{t: t, declName: dn})
			}
		})
	}

	// Sort output types so that errors about cycles are consistent.
	sort.Slice(roots, func(i, j int) bool {
		si := types.TypeString(roots[i].t, nil) + roots[i].declName
		sj := types.TypeString(roots[j].t, nil) + roots[j].declName
		return si < sj
	})

	for _, root := range roots {
		// Depth-first search using a stack of trails through the provider map.
		stk := [][]graphNode{{root}}
		for len(stk) > 0 {
			curr := stk[len(stk)-1]
			stk = stk[:len(stk)-1]
			head := curr[len(curr)-1]

			m := visited.At(head.t)
			if m == nil {
				m = make(map[string]bool)
				visited.Set(head.t, m)
			}
			mm := m.(map[string]bool)
			if mm[head.declName] {
				continue
			}
			mm[head.declName] = true

			pt := set.forWithDeclName(head.t, head.declName)
			if pt.IsNil() {
				// Leaf: input.
				continue
			}

			var args []graphNode
			switch {
			case pt.IsValue():
				// Leaf: values do not have dependencies.
			case pt.IsArg():
				// Injector arguments do not have dependencies.
			case pt.IsProvider() || pt.IsField():
				if pt.IsProvider() {
					for _, arg := range pt.Provider().Args {
						dn := ""
						if arg.Decl != nil {
							if arg.Decl.Pkg() != nil {
								dn = arg.Decl.Pkg().Path() + "." + arg.Decl.Name()
							} else {
								dn = arg.Decl.Name()
							}
						}
						args = append(args, graphNode{t: arg.Type, declName: dn})
					}
				} else {
					args = append(args, graphNode{t: pt.Field().Parent, declName: ""})
				}
				for _, a := range args {
					hasCycle := false
					for i, b := range curr {
						if types.Identical(a.t, b.t) && a.declName == b.declName {
							sb := new(strings.Builder)
							fmt.Fprintf(sb, "cycle for %s:\n", types.TypeString(a.t, nil))
							for j := i; j < len(curr); j++ {
								t := set.forWithDeclName(curr[j].t, curr[j].declName)
								if t.IsProvider() {
									p := t.Provider()
									fmt.Fprintf(sb, "%s (%s.%s) ->\n", types.TypeString(curr[j].t, nil), p.Pkg.Path(), p.Name)
								} else {
									p := t.Field()
									fmt.Fprintf(sb, "%s (%s.%s) ->\n", types.TypeString(curr[j].t, nil), p.Parent, p.Name)
								}
							}
							fmt.Fprintf(sb, "%s", types.TypeString(a.t, nil))
							ec.add(errors.New(sb.String()))
							hasCycle = true
							break
						}
					}
					if !hasCycle {
						next := append(append([]graphNode(nil), curr...), a)
						stk = append(stk, next)
					}
				}
			default:
				panic("invalid provider map value")
			}
		}
	}
	return ec.errors
}

// bindingConflictError creates a new error describing multiple bindings
// for the same output type.
func bindingConflictError(fset *token.FileSet, typ types.Type, set *ProviderSet, cur, prev *providerSetSrc) error {
	sb := new(strings.Builder)
	if set.VarName != "" {
		fmt.Fprintf(sb, "%s has ", set.VarName)
	}
	fmt.Fprintf(sb, "multiple bindings for %s\n", types.TypeString(typ, nil))
	fmt.Fprintf(sb, "current:\n<- %s\n", strings.Join(cur.trace(fset, typ), "\n<- "))
	fmt.Fprintf(sb, "previous:\n<- %s", strings.Join(prev.trace(fset, typ), "\n<- "))
	return notePosition(fset.Position(set.Pos), errors.New(sb.String()))
}
