import TheCount.Data.List

inductive Lit (ν : Type)
  | pos (x : ν)
  | neg (x : ν)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Lit

instance [ToString ν] : ToString (Lit ν) :=
  ⟨fun
    | pos x => toString x
    | neg x => "-" ++ toString x⟩

instance [Hashable ν] : Hashable (Lit ν) where
  hash := fun
    | pos x => mixHash 0 (hash x)
    | neg x => mixHash 1 (hash x)

def negate : Lit ν → Lit ν
  | pos x => neg x
  | neg x => pos x

instance : Neg (Lit ν) :=
  ⟨negate⟩

def var : Lit ν → ν
  | pos x => x
  | neg x => x

def polarity : Lit ν → Bool
  | pos _ => true
  | neg _ => false

def ofDimacs? (s : String) : Option (Lit String) :=
  if s.isEmpty then none
  else if s[0] == '-' then neg (s.drop 1)
  else pos s

def ofInt (i : Int) : Lit Nat :=
  if i < 0 then Lit.neg i.natAbs
  else Lit.pos i.natAbs

end Lit

def LitList ν := List (Lit ν)

namespace LitList

instance [Repr ν] : Repr (LitList ν) := inferInstanceAs (Repr (List _))
instance [DecidableEq ν] : DecidableEq (LitList ν) := inferInstanceAs (DecidableEq (List _))
instance [BEq ν] : BEq (LitList ν) := inferInstanceAs (BEq (List _))
instance [Inhabited ν] : Inhabited (LitList ν) := inferInstanceAs (Inhabited (List _))

instance [Hashable ν] : Hashable (LitList ν) where
  hash C := C.map Hashable.hash |>.foldl mixHash 0

instance : ForIn m (LitList ν) (Lit ν) :=
  inferInstanceAs (ForIn m (List _) _)

instance : Append (LitList ν) :=
  inferInstanceAs (Append (List _))

-- TODO(WN): To optimize, write C impl with bitfields and SAT magic
def mk (ls : List (Lit ν)) : LitList ν := ls

end LitList

/-- A partial assignment of truth values. -/
def PropAssignment ν := LitList ν

namespace PropAssignment 

instance [Repr ν] : Repr (PropAssignment ν) := inferInstanceAs (Repr (LitList _))
instance [DecidableEq ν] : DecidableEq (PropAssignment ν) := inferInstanceAs (DecidableEq (LitList _))
instance [BEq ν] : BEq (PropAssignment ν) := inferInstanceAs (BEq (LitList _))
instance [Inhabited ν] : Inhabited (PropAssignment ν) := inferInstanceAs (Inhabited (LitList _))
instance [Hashable ν] : Hashable (PropAssignment ν) := inferInstanceAs (Hashable (LitList _))
instance : ForIn m (PropAssignment ν) (Lit ν) := inferInstanceAs (ForIn m (LitList _) _)
instance : Append (PropAssignment ν) := inferInstanceAs (Append (LitList _))

instance [ToString ν] : ToString (PropAssignment ν) where
  toString := fun
    | [] => ""
    | ls => ", ".intercalate <| ls.map ToString.toString

def mk : List (Lit ν) → PropAssignment ν := LitList.mk

def extend : Lit ν → PropAssignment ν → PropAssignment ν :=
  List.cons

/-- Return the truth value of `x` at `τ` if assigned, otherwise `none`. -/
def evalVar? [BEq ν] (τ : PropAssignment ν) (x : ν) : Option Bool := Id.run do
  for l in τ do
    if l.var == x then return l.polarity
  return none

/-- Evaluate at `x` the total assignment extending `τ` with `⊥` for unassigned variables. -/
def evalVar [BEq ν] (τ : PropAssignment ν) (x : ν) : Bool :=
  τ.evalVar? x |>.getD false

/-- See `evalVar?`. -/
def evalLit? [BEq ν] (τ : PropAssignment ν) (l : Lit ν) : Option Bool :=
  τ.evalVar? l.var |>.map (/- ⇒ -/ if · then l.polarity else ¬l.polarity)

/-- See `evalLit?`. -/
def evalLit [BEq ν] (τ : PropAssignment ν) (l : Lit ν) : Bool :=
  /- ⇔ -/ if τ.evalVar l.var then l.polarity else ¬l.polarity

end PropAssignment

def Clause ν := LitList ν

namespace Clause

instance [Repr ν] : Repr (Clause ν) := inferInstanceAs (Repr (LitList _))
instance [DecidableEq ν] : DecidableEq (Clause ν) := inferInstanceAs (DecidableEq (LitList _))
instance [BEq ν] : BEq (Clause ν) := inferInstanceAs (BEq (LitList _))
instance [Inhabited ν] : Inhabited (Clause ν) := inferInstanceAs (Inhabited (LitList _))
instance [Hashable ν] : Hashable (Clause ν) := inferInstanceAs (Hashable (LitList _))
instance : ForIn m (Clause ν) (Lit ν) := inferInstanceAs (ForIn m (LitList _) _)
instance : Append (Clause ν) := inferInstanceAs (Append (LitList _))

instance [ToString ν] : ToString (Clause ν) where
  toString := fun
    | [] => "⊥"
    | ls => " ∨ ".intercalate <| ls.map ToString.toString

def mk : List (Lit ν) → Clause ν := LitList.mk

def firstLit? : Clause ν → Option (Lit ν) :=
  List.head?

def unit? : Clause ν → Option (Lit ν)
  | [a] => some a
  | _ => none

def isUnit (C : Clause ν) : Bool :=
  C.unit?.isSome

def isEmpty : Clause ν → Bool :=
  List.isEmpty

end Clause

-- returns `none` when the clause reduced to `true`
def PropAssignment.reduceClause [BEq ν] (τ : PropAssignment ν) (C : Clause ν) : Option (Clause ν) :=
  go C
where
  go : Clause ν → Option (Clause ν)
    | [] => some []
    | l :: ls => match τ.evalLit? l with
      | some true => none
      | some false => go ls
      | none => go ls |>.map (l :: ·)

def CnfForm ν := List (Clause ν)

namespace CnfForm

instance [Repr ν] : Repr (CnfForm ν) := inferInstanceAs (Repr (List _))
instance [DecidableEq ν] : DecidableEq (CnfForm ν) := inferInstanceAs (DecidableEq (List _))
instance [BEq ν] : BEq (CnfForm ν) := inferInstanceAs (BEq (List _))
instance [Inhabited ν] : Inhabited (CnfForm ν) := inferInstanceAs (Inhabited (List _))

instance [ToString ν] : ToString (CnfForm ν) where
  toString := fun
    | [] => "⊤"
    | Cs => " ∧ ".intercalate <| Cs.map ("(" ++ ToString.toString · ++ ")")

instance [Hashable ν] : Hashable (Clause ν) where
  hash C := C.map Hashable.hash |>.foldl mixHash 0

instance : ForIn m (CnfForm ν) (Clause ν) :=
  inferInstanceAs (ForIn m (List _) _)

instance : Append (CnfForm ν) :=
  inferInstanceAs (Append (List _))

-- TODO(WN): potential optimized impl
def mk (Cs : List (Clause ν)) : CnfForm ν := Cs

-- def disj (φ₁ φ₂ : CnfForm ν) : CnfForm ν :=
--   sorry

def conj [BEq ν] [Hashable ν] (φ₁ φ₂ : CnfForm ν) : CnfForm ν :=
  CnfForm.mk <| List.union φ₁ φ₂

def maxVar? [rel : LT ν] [DecidableRel fun a b : ν  => a < b] (cnf : CnfForm ν) : Option ν :=
  cnf.filterMap (·.map (·.var) |>.maximum?) |>.maximum?

end CnfForm

def PropAssignment.reduceCnf [BEq ν] (τ : PropAssignment ν) (φ : CnfForm ν) : CnfForm ν :=
  go φ
where go : CnfForm ν → (CnfForm ν)
  | [] => []
  | C :: Cs => match τ.reduceClause C with
    | some [] => [[]]
    | some C' => C' :: go Cs
    | none => go Cs