import Std.Data.HashMap

import Lean.Meta.Basic
import Lean.Elab.Command

import LeanSat.Data.Sexp
import LeanSat.Dsl.Sexp
import LeanSat.Playground.SmtSolvers

/-! This module attempts to translate certain Lean expressions to SMTLIB expressions. Satisfiability
can then be checked.

Planned features:
- Recursive translation of definitions appearing in an expression.
- Partial elimination of higher-order structure with values of known "shape" through reduction
  (in the kernel or custom). For example, `List.all (· == 1) [a,b]` contains a higher-order lambda,
  but reduces to the first-order `a == 1 ∧ a == b`. Custom reduction might be needed to support
  `partial` definitions with no terminating values in the type theory.
- Encoding of universal quantifiers into quantifier-free (`QF`) theories via constants.
- Good support for bitvectors and `QF_BV`.

Potential features:
- Encoding existential quantifiers with skolemization.
- Encoding rank-1 polymorphic definitions via λ-lifting and combinators, similarly to what is done
  for Isabelle/HOL and HOL Light. [1]
- Model reconstruction.
- Unsatisfiability proof reconstruction.

Limitations:
- Support for value-indexed types (or otherwise "very-dependent" ones) is not planned.

[1] https://matryoshka-project.github.io/pubs/seventeen.pdf -/

open Lean (Name MetaM)

set_option autoImplicit false

private constant TranslationExtRefPointed : NonemptyType.{0}

private def TranslationExtRef : Type := TranslationExtRefPointed.type

instance : Nonempty TranslationExtRef := TranslationExtRefPointed.property

structure TranslationState where
  -- Each entry is a type name translated to an SMT sort.
  -- TODO(WN): quotient keys by defeq with a discrimination tree?
  -- TODO(WN): this can't simply be a namemap. For example, we may want
  -- BitVec n => _ BV n
  -- Maybe a typeclass for extensibility? -/
  -- sortMap : Std.HashMap Name String
  -- TODO(WN): could readd the sortMap if we want to support ADTs

  /-- Each entry is a translation of a Lean value. We take:
  - `def` to `define-fun`(`-rec`)
  - `constant` to `declare-const` or `declare-fun` -/
  valMap : Std.HashMap Name String

  exts : Array TranslationExtRef

/-- We define a `TranslationM` monad which keeps track of which Lean constants have been
translated to which SMT expressions. -/
abbrev TranslationM := StateT TranslationState <| MetaM

namespace TranslationM

open Lean Meta

/-- Extends base translation capabilities with new primitives. Used to support particular theories,
and potential user extensions. -/
structure TranslationExt where
  translateSort : Expr → TranslationM (Option Sexp)
  translateVal  : Expr → TranslationM (Option Sexp)
  deriving Inhabited

unsafe def mkTranslationExtImp (ext : TranslationExt) : TranslationExtRef :=
  unsafeCast ext

@[implementedBy mkTranslationExtImp]
constant mkTranslationExt (ext : TranslationExt) : TranslationExtRef

instance : Inhabited TranslationExtRef where
  default := mkTranslationExt default

unsafe def getExtsImp : TranslationM (Array TranslationExt) :=
  return (← get).exts.map unsafeCast

@[implementedBy getExtsImp]
constant getExts : TranslationM (Array TranslationExt)

def addExt (ext : TranslationExt) : TranslationM Unit := do
  modify fun st => { st with exts := st.exts.push (mkTranslationExt ext) }

def translateSort (e : Expr) : TranslationM Sexp := do
  for ext in ← getExts do
    if let some s ← ext.translateSort e then return s

  -- if let some nm := expr.constName? then
  -- if let some sortNm := (← get).sortMap.find? nm
  -- then return sortNm

  throwError "type {e} has no corresponding SMT-LIB sort"

/-- Translate an `.fvar` into an SMT-LIB `sorted_var`. -/
def translateSortedFVar (e : Expr) : TranslationM Sexp :=
  if let .fvar _ _ := e then do
    let fv ← getFVarLocalDecl e
    let tp ← inferType e
    return sexp!{({toString fv.userName} {← translateSort tp})}
  else unreachable!

partial def translateVal (e : Expr) : TranslationM Sexp :=
  go e
where go (e : Expr) : TranslationM Sexp := do
  for ext in ← getExts do
    if let some s ← ext.translateVal e then return s

  match e with
  | .const nm _ _ => do
    return .atom (toString nm)
    -- if let some val := (← get).valMap.find? nm
    --   then return .atom val
    -- throwError "constant '{nm}' has no corresponding SMT-LIB"
  | e@(.fvar _ _) => do
    let nm ← (toString ∘ LocalDecl.userName) <$> getFVarLocalDecl e
    return .atom nm
  | e@(.app _ _ _) => e.withApp fun fn args => do
    let fnSmt ← go fn
    let argsSmt ← args.mapM go
    return sexp!{({fnSmt} ...{argsSmt.toList})}
  | .lam x xTp body _ => do
    throwError "cannot translate lambda to SMT-LIB"
  | .letE _ _ _ _ _ => throwError "TODO"
  | .lit _ _ => throwError "TODO"
  | .mdata _ e _ => go e
  | e@(.forallE _ _ _ _) => do
    forallTelescopeReducing e fun args tp => do
      let binders ← args.mapM translateSortedFVar
      return sexp!{(forall (...{binders.toList}) {← go tp})}
  | e => throwError "cannot translate expression {e} to SMT-LIB"

def setValFor (valNm : Name) (val : String) : TranslationM Unit := do
  modify fun st => { st with valMap := st.valMap.insert valNm val }

open Lean Meta in
def translateDef (constName : Name) : TranslationM Sexp := do
  let .defnInfo defInfo ← getConstInfo constName | throwError "'{constName}' is not a 'def'"
  if defInfo.safety != .«safe» then throwError "'{constName}' is not safe"
  forallTelescopeReducing defInfo.type fun args bodyTp => do
    let binders ← args.mapM translateSortedFVar
    let bodySort ← translateSort bodyTp
    lambdaTelescope defInfo.value fun args' body => do
      if args.size != args'.size then
        throwError "argument and type telescopes don't match: {args} and {args'}"

      let nm := toString constName
      setValFor constName nm

      return sexp!{
        (define-fun {nm} (...{binders.toList}) {bodySort}
          {← translateVal body})
      }

def translateDefs (nms : Array Name) : TranslationM (Array Sexp) := do
  let mut ret := #[]
  for nm in nms do
    ret := ret.push <| ← translateDef nm
  return ret

/-- Add support for the Core theory to the translation. -/
def addTheoryCore : TranslationM Unit :=
  let translateSort (e : Expr) : TranslationM (Option Sexp) :=
    if e.isProp || e.constName? matches some ``Bool then return some "Bool"
    else return none

  -- TODO how can we use discr trees here instead of nested ifs?
  let translateVal (e : Expr) : TranslationM (Option Sexp) := do
    match e.constName? with
    | some nm => match nm with
      | ``true | ``True => return some "true"
      | ``false | ``False => return some "false"
      | _ => return none
    | none =>
      -- TODO ne, iff, ite, distinct
      -- TODO boolean operations
      if let some arg := e.not? then
        return some sexp!{(not {← translateVal arg})}
      if let some (p, q) := e.and? then
        return some sexp!{(and {← translateVal p} {← translateVal q})}
      if let some (p, q) := e.app2? ``Or then
        return some sexp!{(or {← translateVal p} {← translateVal q})}
      if let some (p, q) := e.arrow? then
        if (← inferType e).isProp then
          return some sexp!{(=> {← translateVal p} {← translateVal q})}
      if let some (_, a, b) := e.eq? then
        return some sexp!{(= {← translateVal a} {← translateVal b})}
      return none

  addExt { translateSort, translateVal }

def ofNatNumeral? (e : Expr) : Option Nat := do
  let some (_, n, _) := e.app3? ``OfNat.ofNat | none
  let some n := n.natLit? | none
  return n

@[inline] def app6? (e : Expr) (fName : Name) : Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity fName 6 then
    some (
      e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appFn!.appArg!,
      e.appFn!.appFn!.appArg!,
      e.appFn!.appArg!,
      e.appArg!
    )
  else
    none

/-- Add support for the Ints theory to the translation. -/
def addTheoryInts : TranslationM Unit :=
  -- TODO how can we use discr trees here instead of nested ifs?
  let translateSort (e : Expr) : TranslationM (Option Sexp) :=
    if e.constName? matches some ``Int then return some "Int"
    else return none

  -- TODO hadd, hsub, hmul, hdiv etc
  let translateVal (e : Expr) : TranslationM (Option Sexp) := do
    if let some n := ofNatNumeral? e then
      return toString n
    if let some (_, _, a) := e.app3? ``Neg.neg then
      return some sexp!{(- {← translateVal a})}
    if let some (_, _, a, b) := e.app4? ``Sub.sub then
      return some sexp!{(- {← translateVal a} {← translateVal b})}
    if let some (_, _, _, _, a, b) := app6? e ``HSub.hSub then
      return some sexp!{(- {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``Add.add then
      return some sexp!{(+ {← translateVal a} {← translateVal b})}
    if let some (_, _, _, _, a, b) := app6? e ``HAdd.hAdd then
      return some sexp!{(+ {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``Mul.mul then
      return some sexp!{(* {← translateVal a} {← translateVal b})}
    if let some (_, _, _, _, a, b) := app6? e ``HMul.hMul then
      return some sexp!{(* {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``Div.div then
      return some sexp!{(div {← translateVal a} {← translateVal b})}
    if let some (_, _, _, _, a, b) := app6? e ``HDiv.hDiv then
      return some sexp!{(div {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``Mod.mod then
      return some sexp!{(mod {← translateVal a} {← translateVal b})}
    if let some (_, _, _, _, a, b) := app6? e ``HMod.hMod then
      return some sexp!{(mod {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``LE.le then
      return some sexp!{(<= {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``LT.lt then
      return some sexp!{(< {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``GE.ge then
      return some sexp!{(>= {← translateVal a} {← translateVal b})}
    if let some (_, _, a, b) := e.app4? ``GT.gt then
      return some sexp!{(> {← translateVal a} {← translateVal b})}
    return none

  addExt { translateSort, translateVal }

syntax (name := smt) "smt!" : tactic
open Lean Elab Tactic in
@[tactic smt]
def smtTac : Tactic
  | stx@`(tactic| smt!) => do
    let goalTp ← getMainTarget
    let translateGoal : TranslationM (List Sexp) :=
      forallTelescopeReducing goalTp fun xs tp => do
        addTheoryCore
        addTheoryInts
        let mut cmds := #[]
        for x in xs do
          let tp ← inferType x
          let nm ← LocalDecl.userName <$> Meta.getFVarLocalDecl x
          cmds := cmds.push sexp!{(declare-const {toString nm} {← translateSort tp})}
        cmds := cmds.push sexp!{(assert {← translateVal tp})}
        return cmds.toList
    let st : TranslationState := {
      -- sortMap := Std.HashMap.empty.insert ``Int "Int"
      valMap := Std.HashMap.empty
      exts := #[]
    }
    let cmds ← translateGoal.run' st
    for cmd in cmds do
      logInfo <| toString cmd
  | _ => throwUnsupportedSyntax

end TranslationM

open Lean Elab Command in
elab "#smtlib" ts:term,* : command => do
  let st : TranslationState := {
    -- sortMap := Std.HashMap.empty.insert ``Int "Int"
    valMap := Std.HashMap.empty
    exts := #[]
  }
  let ts := ts.getElems
  liftTermElabM none do
    let mut st := st
    let (_, st') ← liftM <| TranslationM.addTheoryCore |>.run st
    st := st'
    let (_, st') ← liftM <| TranslationM.addTheoryInts |>.run st
    st := st'
    for t in ts do
      if t.isIdent then
        let (smt, st') ← liftM <| TranslationM.translateDef t.getId |>.run st
        st := st'
        logInfo <| toString smt
      else
        let e ← Term.elabTerm t none
        let (smt, st') ← liftM <| TranslationM.translateVal e |>.run st
        st := st'
        logInfo <| toString smt
      
open TranslationM

def fooConst : Int := 1337

def fooId (x : Int) : Int := x

def fooTwo (x y : Int) : Int := y

def fooTwo' (x y : Int) : Int := fooTwo x y

def fooArith (x y : Int) : Int := (x + y) * fooId x

def fooArith' (x y : Int) : Int := x * (y + x)

def bar (x : List Int) : List Int := List.filter (· == 1) x

#smtlib fooConst, fooId, fooTwo, fooTwo', (∀ x y, fooTwo' x y = fooTwo x y), fooArith, fooArith'

example : ∀ x y, fooTwo' x y = fooTwo x y := by
  smt!
  intro x y
  rfl

#eval callZ3 (verbose := true) sexps!{
  (set-logic LIA)
  (set-option :produce-models true)

  (define-fun fooConst () Int 1337)
  (define-fun fooId ((x Int)) Int x)
  (define-fun fooTwo ((x Int) (y Int)) Int y)
  (define-fun fooArith ((x Int) (y Int)) Int (* (+ x y) (fooId x)))
  (define-fun fooArith_ ((x Int) (y Int)) Int (* x (+ y x)))
  (declare-const a Int)
  (declare-const b Int)
  (assert (not (= (fooArith a b) (fooArith_ a b))))
  -- (assert (not (= fooArith fooArith_)))

  (check-sat)
  (get-model)
}