import Signatures
import Proofs

/-! `Signatures/` is the review surface. Every constant a public statement's type
mentions is defined there, except the execution-model interface below: the word
machine's `Configuration`/`OptionCode`, the weighted-scheme `Index`, and the
family-resource records of the abstract backend, which still live beside their
proofs in `Proofs/Runtime`. Anything new leaking into `Proofs/` fails here.

Imports are checked too: a review module may import `Proofs/` only if it is a
statement (its proof lives there), a resource record (`*Parameters`, `*Resources`,
`*SecurityModel`, `*ExecutionModel`: it bundles budgets derived from the executed
reductions), or a hardness-family hypothesis (`Runtime/*DLogFamily`, phrased over
the backend's configuration). Games, schemes, specifications and models import
only the review surface. -/

open Lean Meta

namespace SignaturesTest.ReviewSurface

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def isStatementModule (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Signatures." && (s.endsWith ".Statement" || s.endsWith "FamilyStatement")

/-- Execution-model vocabulary the statements name directly but that is defined in `Proofs/`. -/
def executionModelInterface : List Name := [
  ``Signatures.Runtime.BackendProgram.OptionCode, ``Signatures.Runtime.BackendProgram.Configuration,
  ``Signatures.Runtime.SchnorrAGM.Native.Interface.SourceRequest,
  ``Signatures.Runtime.WeightedAGM.Index.oops, ``Signatures.Runtime.WeightedAGM.Index.proximity,
  ``Signatures.Runtime.WeightedCaliper.Family.dlogHardness,
  ``Signatures.Runtime.WeightedCaliper.Family.PolynomialResources,
  ``Signatures.Runtime.WeightedAGM.General.Family.PolynomialResources,
  ``Signatures.Runtime.WeightedAGM.General.Parameters.configuration,
  ``Signatures.Runtime.WeightedAGM.General.Parameters.generator,
  ``Signatures.Runtime.WeightedAGM.General.Parameters.inputWidth,
  ``Signatures.Runtime.WeightedAGM.General.Parameters.keyGenerator,
  ``Signatures.Runtime.WeightedAGM.General.Parameters.rep]

run_meta do
  let env ← getEnv
  let isProof (n : Name) : Bool := match moduleOf env n with
    | some m => m.toString.startsWith "Proofs."
    | none => false
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternal then continue
    if let some m := moduleOf env n then
      if isStatementModule m then
        if let .thmInfo _ := ci then roots := roots.push n
  unless 20 ≤ roots.size do throwError "expected the public statements, found {roots.size}"
  let mut leaks : Array (Name × Name) := #[]
  let mut interfaceUsed : NameSet := {}
  for r in roots do
    for c in (← getConstInfo r).type.getUsedConstants do
      if isProof c then
        if executionModelInterface.contains c then interfaceUsed := interfaceUsed.insert c
        else leaks := leaks.push (r, c)
  unless leaks.isEmpty do throwError "statements name definitions from Proofs/: {leaks.toList}"
  for c in executionModelInterface do
    unless interfaceUsed.contains c do
      throwError "{c} is no longer named by any statement; remove it from the interface list"
  logInfo m!"review surface: {roots.size} public statements name only Signatures/ definitions and the {executionModelInterface.length} execution-model interface constants"

/-- Review modules allowed to import `Proofs/`. -/
def mayImportProofs (m : Name) : Bool :=
  let s := m.toString
  s.endsWith "Statement" || s.endsWith "Statements" || s.endsWith "Parameters" || s.endsWith "Resources" ||
    s.endsWith "SecurityModel" || s.endsWith "ExecutionModel" || s.startsWith "Signatures.Runtime."

run_meta do
  let env ← getEnv
  let mut leaks : Array (Name × Name) := #[]
  for h : idx in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[idx]
    unless m.toString.startsWith "Signatures." && !mayImportProofs m do continue
    for imp in env.header.moduleData[idx]!.imports do
      if imp.module.toString.startsWith "Proofs." then leaks := leaks.push (m, imp.module)
  unless leaks.isEmpty do throwError "review modules importing Proofs/: {leaks.toList}"

end SignaturesTest.ReviewSurface
