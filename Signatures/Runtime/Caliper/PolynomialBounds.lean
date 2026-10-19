import Signatures.Runtime.PolynomialResources

/-! Arithmetic closure for parameter-indexed Caliper resource formulas. The
small tactic constructs ordinary proof terms from the closure lemmas below;
it never assumes that an opaque operation has polynomial cost. -/
namespace Signatures.Runtime.PolynomiallyBounded

theorem max {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => by omega)

theorem sub {f g : Nat → Nat} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => f n - g n) := hf.of_le (fun _ => Nat.sub_le _ _)

theorem succ {f : Nat → Nat} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => (f n).succ) := hf.add (const 1)

theorem ite {f g : Nat → Nat} (condition : Nat → Prop) [∀ n, Decidable (condition n)]
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => if condition n then f n else g n) :=
  (hf.max hg).of_le (fun n => by split <;> simp)

end Signatures.Runtime.PolynomiallyBounded

namespace Signatures.Runtime.CaliperBackend
open Lean Meta Elab Tactic

/-- Share proofs of repeated subexpressions instead of expanding the same
layout widths at every occurrence in a generated resource formula. -/
private partial def polynomialProof (parameter : Expr) (hypotheses : Array Expr)
    (body : Expr) : StateT (Std.HashMap Expr Expr) MetaM Expr := do
  let body := body.headBeta.consumeMData
  if let some proof := (← get)[body]? then return proof
  let function ← mkLambdaFVars #[parameter] body
  for hypothesis in hypotheses do
    let type ← inferType hypothesis
    let candidate := type.getAppArgs[0]!
    let candidateBody := (mkApp candidate parameter).headBeta.consumeMData
    if candidateBody == body ||
        (candidateBody.getAppFn == body.getAppFn &&
          (← withReducible (isDefEq candidate function))) then
      modify (·.insert body hypothesis)
      return hypothesis
  let proof ← do
    if (body.find? (· == parameter)).isNone then
      mkAppM ``PolynomiallyBounded.const #[body]
    else if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Nat.add ||
        body.isAppOf ``HMul.hMul || body.isAppOf ``Nat.mul ||
        body.isAppOf ``Max.max || body.isAppOf ``Nat.max then
      let args := body.getAppArgs
      let left ← polynomialProof parameter hypotheses args[args.size - 2]!
      let right ← polynomialProof parameter hypotheses args[args.size - 1]!
      let rule := if body.isAppOf ``HAdd.hAdd || body.isAppOf ``Nat.add then ``PolynomiallyBounded.add
        else if body.isAppOf ``HMul.hMul || body.isAppOf ``Nat.mul then ``PolynomiallyBounded.mul
        else ``PolynomiallyBounded.max
      mkAppM rule #[left, right]
    else if body.isAppOf ``HSub.hSub || body.isAppOf ``Nat.sub then
      let args := body.getAppArgs
      let left ← polynomialProof parameter hypotheses args[args.size - 2]!
      let right ← mkLambdaFVars #[parameter] args[args.size - 1]!
      mkAppOptM ``PolynomiallyBounded.sub #[none, some right, some left]
    else if body.isAppOf ``Nat.succ then
      mkAppM ``PolynomiallyBounded.succ #[← polynomialProof parameter hypotheses body.getAppArgs[0]!]
    else if body.isAppOf ``ite then
      let args := body.getAppArgs
      let condition ← mkLambdaFVars #[parameter] args[1]!
      let decidable ← mkLambdaFVars #[parameter] args[2]!
      let left ← polynomialProof parameter hypotheses args[3]!
      let right ← polynomialProof parameter hypotheses args[4]!
      mkAppOptM ``PolynomiallyBounded.ite #[none, none, some condition, some decidable, some left, some right]
    else
      let next? ← match body with
        | .letE _ _ value rest _ => pure (some (rest.instantiate1 value))
        | .proj .. => withTransparency .default (reduceProj? body)
        | _ => unfoldDefinition? body (ignoreTransparency := true)
      if let some next := next? then
        if next == body then throwError "stuck polynomial component {body}"
        polynomialProof parameter hypotheses next
      else
        let mut found := none
        for hypothesis in hypotheses do
          let type ← inferType hypothesis
          if ← withTransparency .default (isDefEq type.getAppArgs[0]! function) then
            found := some hypothesis
            break
        let some proof := found | throwError "missing polynomial component bound for {body}"
        pure proof
  modify (·.insert body proof)
  return proof

/-- Prove a numerical resource formula using local polynomial bounds and
arithmetic closure. Opaque costs without a hypothesis remain errors. All
constructed proof terms are checked by Lean's kernel. -/
elab "caliper_polynomial" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``PolynomiallyBounded do
    throwError "expected a polynomial resource bound"
  let resource := target.getAppArgs[0]!
  let mut hypotheses := #[]
  for declaration in ← getLCtx do
    if !declaration.isImplementationDetail && declaration.type.consumeMData.isAppOf ``PolynomiallyBounded then
      hypotheses := hypotheses.push declaration.toExpr
  let proof ← withLocalDeclD `parameter (mkConst ``Nat) fun parameter => do
    (polynomialProof parameter hypotheses (mkApp resource parameter).headBeta).run' {}
  closeMainGoal `caliper_polynomial proof

end Signatures.Runtime.CaliperBackend
