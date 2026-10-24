import Proofs.Runtime.BackendSchnorrPrivateSamplingDescription
import Proofs.Runtime.BackendSchnorrPrivateSamplingBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! The implemented sampler transformation shares the raw tape across adaptive
draws, retained local contexts and both loop forms. A skipped branch must leave
the tape untouched. These examples execute actual assembled code denotations. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr Signatures.Runtime.Schnorr.RawTape

namespace SignaturesTest.SchnorrPrivateSampling

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))

private def tape : List (TapeCell F) := [(4, 0, 1), (3, 0, 0), (4, 0, 2)]

/-- The second arity depends on the first reply. A later arity-two cell remains
available for the attacker's next private request. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (.seq (UniformSampling.code rep.data uniform) (UniformSampling.code rep.data uniform))).denote
      (2, [], tape) = pure (0, [], [(4, 0, 2)]) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (.seq (UniformSampling.code rep.data uniform) (UniformSampling.code rep.data uniform))
    2 (⟨[], tape⟩ : State F)).trans ?_
  simp only [Code.denote, UniformSampling.denote]
  rfl

/-- A retained local value survives while the simulator's tape advances. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (.first rep.data.nat (UniformSampling.code rep.data uniform))).denote
      ((2, 99), [], tape) = pure ((1, 99), [], [(3, 0, 0), (4, 0, 2)]) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (.first rep.data.nat (UniformSampling.code rep.data uniform)) (2, 99) (⟨[], tape⟩ : State F)).trans ?_
  simp only [Code.denote, UniformSampling.denote]
  rfl

/-- Choosing the pure branch consumes no saved private draw. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (.branch (UniformSampling.code rep.data uniform) (.atomic (Q.identity rep.data.nat)))).denote
      (Sum.inr 99, [], tape) = pure (99, [], tape) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (.branch (UniformSampling.code rep.data uniform) (.atomic (Q.identity rep.data.nat)))
    (Sum.inr 99) (⟨[], tape⟩ : State F)).trans ?_
  rfl

/-- Input-counted iteration uses one body description and preserves draw order. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (.iterate rep.data.nat (UniformSampling.code rep.data uniform))).denote
      ((2, 2), [], tape) = pure (0, [], [(4, 0, 2)]) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (.iterate rep.data.nat (UniformSampling.code rep.data uniform)) (2, 2) (⟨[], tape⟩ : State F)).trans ?_
  simp only [Code.denote]
  rfl

/-- Fuel exhaustion executes the original stop code after the two draws. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (.loop (.seq (UniformSampling.code rep.data uniform)
        (.atomic (QS.inr rep.data.nat rep.data.nat))) (.atomic (Q.identity rep.data.nat)) 2)).denote
      (2, [], tape) = pure (0, [], [(4, 0, 2)]) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (.loop (.seq (UniformSampling.code rep.data uniform)
      (.atomic (QS.inr rep.data.nat rep.data.nat))) (.atomic (Q.identity rep.data.nat)) 2)
    2 (⟨[], tape⟩ : State F)).trans ?_
  simp only [Code.denote, UniformSampling.denote]
  rfl

/-- Typed replay normalizes an out-of-range stored value exactly as the source
does; the native source theorem does not silently assume every input tape valid. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (UniformSampling.code rep.data uniform)).denote
      (2, [], [(4, 0, 8)]) = pure (2, [], []) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (UniformSampling.code rep.data uniform) 2 (⟨[], [(4, 0, 8)]⟩ : State F)).trans ?_
  simp only [UniformSampling.denote]
  rfl

/-- Large numeric arities stay runtime data, with one lookup and typed reply. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (UniformSampling.code rep.data uniform)).denote
      (2^64, [], [(2^64 + 2, 0, 7)]) = pure (7, [], []) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (UniformSampling.code rep.data uniform) (2^64) (⟨[], [(2^64 + 2, 0, 7)]⟩ : State F)).trans ?_
  simp only [UniformSampling.denote]
  rfl

/-- A fresh draw appends its raw uniform-family cell after the existing log;
it does not record a separate private scalar event or discard the old prefix. -/
example :
    (NativePrivate.code rep data cost primitive uniform ports
      (UniformSampling.code rep.data uniform)).denote
      (1, [(1, 3, 0)], []) =
      (fun r : Fin 2 => (r.val, [(1, 3, 0), (3, 0, r.val)], [])) <$>
        (unifSpec.query 1 : ProbComp (Fin 2)) := by
  refine (NativePrivate.source rep data cost primitive uniform ports
    (UniformSampling.code rep.data uniform) 1 (⟨[(1, 3, 0)], []⟩ : State F)).trans ?_
  simp only [UniformSampling.denote]
  rfl

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``StateSimulation.compile_denote, ``StateSimulation.compile_description,
      ``NativePrivate.uniform_decoded, ``NativePrivate.handler_denote,
      ``NativePrivate.simulate_source, ``NativePrivate.source, ``NativePrivate.scalar_source,
      ``NativePrivate.handler_description, ``NativePrivate.description, ``NativePrivate.handler_bound,
      ``NativePrivate.runtimeBound_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``NativePrivate.code, ``NativePrivate.handler, ``StateSimulation.compile] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isConstOf ``Nat then
          throwError "{name}: compilation must not enumerate arities or tape capacities"
        for forbidden in #[`Signatures.Runtime.Schnorr.SourceCertificate,
            `Signatures.Runtime.AGM.SourceCertificate, `Signatures.Runtime.Coron.SourceCertificate, ``Program] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: no arithmetic source implementation may be required"
  for name in #[``NativePrivate.uniform_decoded, ``NativePrivate.source, ``NativePrivate.scalar_source] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: the entire computation must agree"
      for param in params do
        if ((← inferType param).find? (fun e => e.isConstOf ``Valid)).isSome then
          throwError "{name}: typed simulation must cover all input tapes"
  forallTelescope (← getConstInfo ``NativePrivate.handler_bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "the native handler must have a complete execution bound"
    for param in params do
      if ((← inferType param).find? (fun e => e.isConstOf ``Bounds)).isSome then
        throwError "the native handler budget must be derived from primitive contracts"
  forallTelescope (← getConstInfo ``NativePrivate.runtimeBound).type fun params _ => do
    for param in params do
      let name := (← getFVarLocalDecl param).userName
      if #[`arityCap, `randomBound, `domainSize].contains name then
        throwError "native runtime must not enumerate the numeric arity or domain"

end SignaturesTest.SchnorrPrivateSampling
