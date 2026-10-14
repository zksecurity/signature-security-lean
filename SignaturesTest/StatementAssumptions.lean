import Signatures
import Lean.Util.CollectAxioms

-- Boolean predicate notation elaborates to the original signing-query selector exactly.
example {L R α : Type} {spec : OracleSpec (L ⊕ R)} (oa : OracleComp spec α) (qS : Nat) :
    OracleComp.IsQueryBoundP oa (·.isRight) qS ↔
      OracleComp.IsQueryBoundP oa (fun i => Sum.isRight i = true) qS := Iff.rfl

-- Uniform sampling already supplies finiteness; the collision denominator stays nonzero.
example {F : Type} [Field F] [SampleableType F] : Nat.card F ≠ 0 :=
  Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

-- The shorter nondegeneracy premise is equivalent, not stronger or weaker.
example {F G : Type} [Field F] [AddCommGroup G] [Module F G] (g : G) :
    Function.Injective (fun c : F => c • g) ↔ g ≠ 0 := by
  constructor
  · intro hinj hz
    exact zero_ne_one (hinj (show (0 : F) • g = (1 : F) • g by simp [hz]))
  · exact smul_left_injective F

-- The former co-CDH premises imply the new ones. The statement's proof adapter
-- checks the converse by reconstructing both former premises.
example {F G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [AlgebraicGroupModel.BilinearPairing F G₁ G₂ Gₜ]
    (g₁ : G₁) (g₂ : G₂)
    (hgen : Function.Bijective (fun c : F => c • g₁))
    (hinj : Function.Injective
      (fun z : G₁ => AlgebraicGroupModel.pairing (F := F) (Gₜ := Gₜ) z g₂)) :
    Function.Surjective (fun c : F => c • g₁) ∧
      (AlgebraicGroupModel.pairing (F := F) g₁ g₂ : Gₜ) ≠ 0 := by
  refine ⟨hgen.2, ?_⟩
  intro hz
  apply zero_ne_one (α := F)
  apply hgen.1
  apply hinj
  simp only [AlgebraicGroupModel.pairing_smul_left, hz, smul_zero]

open Lean Meta Elab Command

-- The native BLS endpoint consumes general caller resources and derives the
-- completed solver certificate. Hardness covers that same backend and explicit
-- input/code/time caps. The probability transport admits arbitrary messages.
run_cmd liftTermElabM do
  let name := ``Signatures.Runtime.Coron.NativeSolver.security_of_resources
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all allowed.contains do
    throwError "{name}: unexpected axiom footprint {axioms}"
  forallTelescope (← getConstInfo name).type fun params _ => do
    let mut sawResources := false
    let mut sawHardness := false
    let mut sawFiniteMessage := false
    let mut sawChallenge := false
    let mut sawDerivedTime := false
    for param in params do
      let binder ← param.fvarId!.getUserName
      let type ← inferType param
      if type.isAppOf ``Signatures.Runtime.BackendProgram.Within ||
          type.isAppOf ``Signatures.Runtime.Coron.SourceCertificate then
        throwError "{name}: finished-solver or arithmetic-source certificate became a premise"
      if binder == `hrun then
        sawResources := type.isAppOf ``PFunctor.DynSystem.DynComputation.QuantitativeRealization.RunsWithin
      if binder == `htime then
        sawDerivedTime := (type.find? (fun e =>
          e.isAppOf ``Signatures.Runtime.Coron.NativeSolver.nativeSolverTime)).isSome
      if binder == `hchallenge then
        sawChallenge := true
      if type.isAppOf ``Fintype || type.isAppOf ``Finite then
        if let .fvar id := type.getAppArgs[0]! then
          if (← id.getUserName) == `M then sawFiniteMessage := true
      if type.isAppOf ``Model.HardWithin then
        let #[_, _, within, _, _] := type.getAppArgs
          | throwError "{name}: malformed hardness assumption"
        sawHardness := within.isAppOf ``Signatures.Runtime.Coron.NativeSolver.coCDHWithin
    if sawFiniteMessage then
      throwError "{name}: finite-message assumption returned"
    unless sawResources && sawHardness && sawChallenge && sawDerivedTime do
      throwError "{name}: incomplete general-caller/resource/hardness scope"

-- Inspect elaborated signatures: classical instance synthesis in application tests
-- could otherwise conceal a redundant requirement.
run_cmd liftTermElabM do
  for name in #[`BLS.CoCDH.PaperAdversary, `BLS.CoCDH.paperExp,
      `BLS.CoCDH.withPaperMap, `BLS.CoCDH.paperExp_withPaperMap,
      `BLS.Statement.bls_eufcma_le_paper_cocdh] do
    if (← getEnv).contains name then
      throwError "Removed map-based BLS declaration remains imported: {name}"
  for name in #[`BLS.Statement.bls_eufcma_le_dlog, `OOPS.Statement.oops_eufcma_le_dlog,
      `Proximity.Statement.proximity_eufcma_le_dlog, `Model.Interactive.LinAlgAdv,
      `BLS.Scheme.blsScheme, `OOPS.Scheme.oopsSchemeMulti, `Proximity.Scheme.proxScheme] do
    if (← getEnv).contains name then
      throwError "Removed public-table declaration remains imported: {name}"
  for name in #[`BLS.Statement.bls_eufcma_le_cocdh,
      `BLS.Statement.bls_eufcma_of_cocdh_hardness,
      `BLS.Statement.bls_lazy_agm_le_dlog, `BLS.Statement.bls_lazy_agm_of_dlog_hardness,
      `OOPS.Statement.oops_lazy_agm_le_dlog, `OOPS.Statement.oops_lazy_agm_of_dlog_hardness,
      `Proximity.Statement.proximity_lazy_agm_le_dlog,
      `Proximity.Statement.proximity_lazy_agm_of_dlog_hardness,
      `OOPS.Statement.oops_call_eufcma_le_dlog, `Proximity.LazyAGM.Noncollision] do
    if (← getEnv).contains name then
      throwError "Removed weaker public security statement remains imported: {name}"

-- Concrete endpoints must consume source certificates, not assume completed solver budgets.
run_cmd liftTermElabM do
  for name in #[``BLS.Statement.bls_eufcma_of_cocdh_machine_hardness,
      ``BLS.Statement.bls_lazy_agm_of_dlog_machine_hardness,
      ``OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness,
      ``Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness] do
    let axioms ← collectAxioms name
    let expected := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.size == expected.size && axioms.all expected.contains do
      throwError "{name}: unexpected axiom footprint {axioms}"
    let coCDH := name == ``BLS.Statement.bls_eufcma_of_cocdh_machine_hardness
    let proximity := name == ``Proximity.Statement.proximity_lazy_agm_of_dlog_machine_hardness
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut sawSource := false
      let mut hardnessCount := 0
      let mut sawGenerator := false
      let mut sawPairing := false
      let mut sawSigningBound := false
      let mut sawMessageFinite := false
      let mut sawQueries := false
      for param in params do
        let binder ← param.fvarId!.getUserName
        if #[`A, `adv, `cost, `randomBound, `localTime, `queries, `gammaLength, `xiLength].contains binder then
          unless (← param.fvarId!.getDecl).binderInfo == .implicit do
            throwError "{name}: source-certificate index {binder} should be inferred"
        if #[`hbudget, `hgood, `hbad, `within, `goodBudget, `badBudget].contains binder then
          throwError "{name}: caller-supplied finished-solver budget {binder}"
        let type ← inferType param
        if binder == `hgen then
          sawGenerator := type.isAppOf ``Function.Surjective
        if binder == `hpair then
          sawPairing := type.isAppOf ``Ne
        if binder == `queries then
          sawQueries := true
          unless ← isDefEq type (← Lean.Elab.Term.elabTerm (← `(Fin 3 → Nat)) none) do
            throwError "{name}: expected random/hash/sign query budgets"
        if coCDH && binder == `hqs then
          sawSigningBound := true
          let .forallE _ (.fvar scalar) body _ := type
            | throwError "{name}: expected a scalar-indexed signing budget"
          unless (← scalar.getUserName) == `F && body.isAppOf ``OracleComp.IsQueryBoundP do
            throwError "{name}: signing budget must range over generated keys"
        if coCDH && (type.isAppOf ``Finite || type.isAppOf ``Fintype) then
          if let .fvar id := type.getAppArgs[0]! then
            sawMessageFinite := (← id.getUserName) == `M
        if type.isAppOf ``DecidableEq then
          let .fvar id := type.getAppArgs[0]! | continue
          if (← id.getUserName) == `Gₜ then
            throwError "{name}: target-group equality belongs to the winning check"
        if binder == `cert then
          sawSource := true
          let expected := if coCDH then ``Signatures.Runtime.Coron.SourceCertificate
            else ``Signatures.Runtime.AGM.SourceCertificate
          -- Public scheme-specific aliases must still reduce to the concrete certificate.
          unless (← whnf type).isAppOf expected do
            throwError "{name}: missing concrete source certificate"
        if type.isAppOf ``Model.HardWithin then
          hardnessCount := hardnessCount + 1
          let #[_, _, within, budget, _] := type.getAppArgs
            | throwError "{name}: malformed budget-scoped hardness assumption"
          let expectedClass := if coCDH then ``Signatures.Runtime.Coron.coCDHWithin
            else ``Signatures.Runtime.AGM.dlogWithin
          let expectedBudget := if coCDH then ``Signatures.Runtime.Coron.SourceCertificate.targetBudget
            else if binder == `hgoodHard then ``Signatures.Runtime.AGM.SourceCertificate.goodBudget
            else ``Signatures.Runtime.AGM.SourceCertificate.badBudget
          unless within.isAppOf expectedClass && budget.isAppOf expectedBudget do
            throwError "{name}: hardness must use the derived machine budget"
        if #[`hnc, `hvand].contains binder then
          throwError "{name}: symbolic noncollision must be proved or measured, not assumed"
      unless sawSource && hardnessCount == (if coCDH then 1 else 2) do
        throwError "{name}: incomplete source/hardness interface"
      unless sawGenerator && sawPairing && sawQueries do
        throwError "{name}: missing group hypotheses or source query budgets"
      unless !coCDH || (sawSigningBound && !sawMessageFinite) do
        throwError "{name}: missing signing bound or finite-message assumption returned"
      if proximity then
        let some (_, lhs, rhs) := conclusion.le? | throwError "{name}: expected a probability bound"
        if lhs.find? (fun e => e.isAppOf ``Proximity.LazyAGM.collisionGame) |>.isSome then
          throwError "{name}: collision must not restrict the original winning event"
        unless (rhs.find? (fun e => e.isAppOf ``Proximity.LazyAGM.collisionGame)).isSome do
          throwError "{name}: missing actual collision probability on the right-hand side"
      if name == ``OOPS.Statement.oops_lazy_agm_of_dlog_machine_hardness then
        let degrees ← params.filterM fun p => return (← p.fvarId!.getUserName) == `d
        unless degrees.size == 1 && (← isDefEq (← inferType degrees[0]!) (mkConst ``Nat)) do
          throwError "{name}: expected one fixed degree for the whole game"
      let args ← params.filterM fun param => do
        return (← param.fvarId!.getDecl).binderInfo.isExplicit
      let application ← mkAppM name args
      unless ← isDefEq (← inferType application) conclusion do
        throwError "{name}: inferred application has the wrong conclusion"
      if (← instantiateMVars application).hasExprMVar then
        throwError "{name}: explicit arguments do not determine the inferred parameters"

-- The bit endpoint must use the actual heap runner, derive its budget, and
-- retain the accumulated sampling allowance in the conclusion.
run_cmd liftTermElabM do
  let name := ``Schnorr.Statement.schnorr_eufcma_of_dlog_bit_hardness
  let axioms ← collectAxioms name
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.size == expected.size && axioms.all expected.contains do
    throwError "{name}: unexpected axiom footprint {axioms}"
  forallTelescope (← getConstInfo name).type fun params conclusion => do
    let mut sawSource := false
    let mut sawHardness := false
    for param in params do
      let binder ← param.fvarId!.getUserName
      let type ← inferType param
      if #[`hbudget, `herror, `hgood, `hbad, `within, `samplingCount].contains binder then
        throwError "{name}: derived implementation obligation became a premise: {binder}"
      if binder == `cert then
        sawSource := type.isAppOf ``Signatures.Runtime.Schnorr.SourceCertificate
      if type.isAppOf ``Model.HardWithin then
        let #[solver, advantage, within, budget, _] := type.getAppArgs
          | throwError "{name}: malformed hardness assumption"
        unless solver.isConstOf ``Signatures.Runtime.HeapMachine.Package &&
            advantage.isAppOf ``Signatures.Runtime.HeapMachine.dlogAdvantage &&
            within.isAppOf ``Signatures.Runtime.HeapMachine.dlogWithin do
          throwError "{name}: hardness must concern executable bit packages"
        unless (budget.find? (·.isAppOf ``Signatures.Runtime.Schnorr.SourceCertificate.targetBudget)).isSome &&
            (budget.find? (·.isAppOf ``Signatures.Runtime.Schnorr.SourceCertificate.bitFactor)).isSome do
          throwError "{name}: missing derived bit-runtime budget"
        let codeBudget := within.getAppArgs.back!
        unless codeBudget.isAppOf ``Signatures.Runtime.HeapMachine.Package.cells &&
            codeBudget.getAppArgs.back!.isAppOf ``Signatures.Runtime.Schnorr.SourceCertificate.bitCode do
          throwError "{name}: static budget must count the actual compiled package"
        for other in params do
          if #[`H₂, `encodeK, `encodeM].contains (← other.fvarId!.getUserName) then
            let id := other.fvarId!
            if advantage.containsFVar id || within.getAppArgs.pop.any (·.containsFVar id) then
              throwError "{name}: DLog challenge interface depends on an unrelated source parameter"
        sawHardness := true
    unless sawSource && sawHardness do
      throwError "{name}: incomplete implementation interface"
    let conclusion ← zetaReduce conclusion
    let some (_, _, rhs) := conclusion.le? | throwError "{name}: expected a probability inequality"
    unless (rhs.find? (·.isAppOf ``Signatures.Runtime.Schnorr.SourceCertificate.targetBudget)).isSome &&
        (rhs.find? (·.isAppOf ``HPow.hPow)).isSome do
      throwError "{name}: missing accumulated bounded-rejection error"
