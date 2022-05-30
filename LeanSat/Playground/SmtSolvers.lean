import Std.Data.AssocList

import LeanSat.Data.Sexp
import LeanSat.Dsl.Sexp

def argsCvc4 : IO.Process.SpawnArgs := {
  cmd := "cvc4"
  args := #["--lang", "smt", "/tmp/temp.smt"] }

def argsCvc5 : IO.Process.SpawnArgs := {
  cmd := "cvc5"
  args := #["--lang", "smt", "/tmp/temp.smt"] }

def argsZ3 : IO.Process.SpawnArgs := {
  cmd := "z3/bin/z3"
  args := #["-smt2", "/tmp/temp.smt"] }

def argsBoolector : IO.Process.SpawnArgs := {
  cmd := "boolector"
  args := #["--smt2", "/tmp/temp.smt"] }

-- Same as IO.Process.run, but does not require exitcode = 0
def run' (args : IO.Process.SpawnArgs) : IO String := do
  let out ← IO.Process.output args
  pure out.stdout

/-- Executes the solver with the provided list of commands in SMT-LIB s-expression format.
Returns the solver output as s-expressions. -/
def callSolver (args : IO.Process.SpawnArgs) (commands : List Sexp) (verbose : Bool := false)
    : IO (List Sexp) := do
  let cmdStr := Sexp.serializeMany commands
  if verbose then
    IO.println "Sending SMT-LIB problem:"
    IO.println cmdStr
  IO.FS.writeFile "/tmp/temp.smt" cmdStr
  let out ← run' args
  if verbose then
    IO.println "\nSolver replied:"
    IO.println out
  let out ← IO.ofExcept (Sexp.parse out)
  return out

def callCvc4 := @callSolver argsCvc4
def callCvc5 := @callSolver argsCvc5
def callZ3 := @callSolver argsZ3
def callBoolector := @callSolver argsBoolector

private def hexdigits : Array Char :=
  #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' ]

def enhexByte (x : UInt8) : String :=
  ⟨[hexdigits.get! $ UInt8.toNat $ (x.land 0xf0).shiftRight 4,
    hexdigits.get! $ UInt8.toNat $ x.land 0xf ]⟩

/-- Convert a little-endian (LSB first) list of bytes to hexadecimal. -/
def enhexLE : List UInt8 → String
  | [] => ""
  | b::bs => enhexLE bs ++ enhexByte b

/-- Converts a number `n` to its hexadecimal SMT-LIB representation as a `nBits`-bit vector.
For example `toBVConst 32 0xf == "#x0000000f"`. -/
def toBVConst (nBits : Nat) (n : Nat) : String :=
  assert! nBits % 8 == 0
  let nBytes := nBits/8
  let bytes := List.range nBytes |>.map fun i => UInt8.ofNat ((n >>> (i*8)) &&& 0xff)
  "#x" ++ enhexLE bytes

open Std (AssocList)

/-- Extracts constants assigned in a model returned from an SMT solver.
The model is expected to be a single s-expression representing a list,
with constant expressions represented by `(define-fun <name> () <type> <body>)`. -/
def decodeModelConsts : Sexp → AssocList String Sexp
  | Sexp.expr ss =>
    ss.foldl (init := AssocList.empty) fun
      | acc, sexp!{(define-fun {Sexp.atom x} () {_} {body})} =>
        acc.insert x body
      | acc, _ => acc
  | _ => AssocList.empty

/-- Evaluates an SMT-LIB constant numeral such as `0` or `#b01` or `#x02`. -/
def evalNumConst : Sexp → Option Nat
  | Sexp.atom s =>
    let s' :=
      if s.startsWith "#b" then "0" ++ s.drop 1
      else if s.startsWith "#x" then "0" ++ s.drop 1
      else s
    Lean.Syntax.decodeNatLitVal? s'
  | Sexp.expr _ => none