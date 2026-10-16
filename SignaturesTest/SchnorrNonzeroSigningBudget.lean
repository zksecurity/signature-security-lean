import Signatures.Runtime.BackendSchnorrNonzeroSigningBudget
import Lean.Util.CollectAxioms

/-! The nonzero signer must derive its complete runtime from original samplers
and primitive operations, with distinct states after all three draws. -/

open Lean Meta Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrNonzeroSigningBudget

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NonzeroSigning.Native.Parts.body_eq,
      ``NonzeroSigning.Native.Parts.commitArgs_cost, ``NonzeroSigning.Native.Parts.repairArgs_cost,
      ``NonzeroSigning.Native.Parts.programArgs_cost, ``NonzeroSigning.Native.Parts.returnValue_cost,
      ``NonzeroSigning.Native.code_bound, ``NonzeroSigning.Native.signingTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  forallTelescope (← getConstInfo ``NonzeroSigning.Native.code_bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "Require a complete execution bound"
    for required in #[``NonzeroSigning.Native.code, ``NonzeroSigning.Native.signingTime,
        ``ListROM.NativeCache.SigningInput, ``ListROM.NativeCache.SigningOutput] do
      unless (conclusion.find? (fun e => e.isConstOf required)).isSome do
        throwError "The conclusion must retain the actual signer, derived time and encoding invariants"
    let mut drawBounds := #[]
    for param in params do
      let name := (← getFVarLocalDecl param).userName
      let type ← inferType param
      for forbidden in #[``NonzeroSigning.Native.code, ``NonzeroSigning.Native.signingTime,
          ``ListROM.NativeCache.signing, ``Program, ``SourceCertificate,
          ``Expression.compile, ``Expression.compileBound] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "Do not assume a finished signing budget or restrict attacker syntax"
      if (type.find? (fun e => e.isConstOf ``Bounds)).isSome then
        drawBounds := drawBounds.push name
        let expected := match name with
          | `hdFirst => #[`fieldDraw, `inv, `firstInv, `firstTime]
          | `hdSecond => #[`fieldDraw, `firstInv, `secondInv, `secondTime]
          | `hdThird => #[`nonzeroDraw, `secondInv, `finalInv, `thirdTime]
          | _ => #[]
        unless expected.size == 4 do
          throwError "Only original sampler budgets may be assumed"
        for required in expected do
          -- Resolve by binder name rather than a concrete backend implementation.
          let mut found := false
          for p in params do
            if (← getFVarLocalDecl p).userName == required then
              found := (type.find? (fun e => e == p)).isSome
          unless found do
            throwError "{name}: missing original sampler/state dependency {required}"
    unless drawBounds == #[`hdFirst, `hdSecond, `hdThird] do
      throwError "Charge all three sequential draws"
  forallTelescope (← getConstInfo ``NonzeroSigning.Native.signingTime_polynomial).type fun params conclusion => do
    unless conclusion.isAppOf ``PolynomiallyBounded &&
        (conclusion.find? (fun e => e.isConstOf ``NonzeroSigning.Native.signingTime)).isSome do
      throwError "Derive polynomial growth for the actual complete signing formula"
    for param in params do
      let type ← inferType param
      for forbidden in #[``NonzeroSigning.Native.signingTime, ``Bounds, ``Program] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "Polynomial closure must start from original resource families"

end SignaturesTest.SchnorrNonzeroSigningBudget
