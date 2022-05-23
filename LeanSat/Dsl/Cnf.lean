import LeanSat.Data.Cnf

-- TODO add namespace and scope syntax, instances

declare_syntax_cat varlit

syntax ident : varlit
syntax "-" ident : varlit
syntax num : varlit
syntax "-" num : varlit

-- TODO generalize to Coe Nat α, or at least to UInt64
macro_rules
  | `(varlit| - $x:ident) => `(Lit.neg (ν := String) $(Lean.quote x.getId.toString))
  | `(varlit| $x:ident) => `(Lit.pos (ν := String) $(Lean.quote x.getId.toString))
  | `(varlit| - $x:num) => `(Lit.neg (ν := Nat) $(Lean.quote x.isNatLit?.get!))
  | `(varlit| $x:num) => `(Lit.pos (ν := Nat) $(Lean.quote x.isNatLit?.get!))

declare_syntax_cat clause
syntax "clause!{" clause "}" : term
syntax varlit+ : clause
syntax "⊥" : clause

def Clause.toStringSpaced [ToString ν] : Clause ν → String
  | [] => "⊥"
  | ls => " ".intercalate (ls.map toString)

def Clause.repr [ToString ν] (C : Clause ν) (_ : Nat) : Std.Format :=
  "clause!{" ++ C.toStringSpaced ++ "}"

instance : Repr (Clause String) := ⟨Clause.repr⟩
instance : Repr (Clause Nat) := ⟨Clause.repr⟩

/-- Clauses over variables of type `Nat` or `String` can be written using `clause!{..}`.
Write `clause!{⊥}` for the empty clause. -/
macro_rules
  | `(clause| ⊥) => `(Clause.mk [])
  | `(clause| $[$args:varlit]*) => `(Clause.mk [ $args,* ])
  | `(clause!{ $C:clause }) => return C

declare_syntax_cat cnf
syntax "cnf!{" cnf "}" : term
syntax clause,+ : cnf
syntax "⊤" : cnf

/-- CNFs over variables of type `Nat` or `String` can be written using `cnf!{..}`.
Write `cnf!{⊤}` for the empty conjunction. -/
macro_rules
  | `(cnf| ⊤) => `(CnfForm.mk [])
  | `(cnf| $[$args:clause],*) => `(CnfForm.mk [ $args,* ])
  | `(cnf!{ $φ:cnf }) => return φ

def CnfForm.repr [ToString ν] : CnfForm ν → Nat → Std.Format
  | [], _ => "cnf!{⊤}"
  | Cs, _ => "cnf!{" ++ ", ".intercalate (Cs.map Clause.toStringSpaced) ++ "}"

instance : Repr (CnfForm String) := ⟨CnfForm.repr⟩
instance : Repr (CnfForm Nat) := ⟨CnfForm.repr⟩

syntax "assign!{" varlit,+ "}" : term

/-- Propositional assignments to variables of type `Nat` or `String`
can be written using `assign!{..}`. -/
macro_rules
  | `( assign!{ $[$vars:varlit],* }) => `(PropAssignment.mk [ $vars,* ])

def PropAssignment.repr [ToString ν] (τ : PropAssignment ν) (_ : Nat) : Std.Format :=
  "assign!{" ++ ", ".intercalate (τ.map toString) ++ "}"

instance : Repr (PropAssignment String) := ⟨PropAssignment.repr⟩
instance : Repr (PropAssignment Nat) := ⟨PropAssignment.repr⟩