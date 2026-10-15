import Signatures.Runtime.BackendSchnorrAGMHandlerDescription
import Signatures.Runtime.BackendSchnorrAGMHandlerPrimitiveBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Schnorr.AGM
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Interface

namespace SignaturesTest.BackendSchnorrAGMHandler

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

section Native

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (bd : Boundary C (sourceSpec F F Nat).toPFunctor F F)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- The dependent reply tag retains the full original hash request, including
-- its coefficients. The cached zero and first explanation remain unchanged.
example : (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
    (request (.hash 7) [1] [[0, 5]], (1, 2), [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], false, true) =
    pure (scalarTag false ((7, [1], [[0, 5]]), (0, [])), (1, 2),
      [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], false, true) := by
  rw [Handler.code_denote]
  simp only [request, Handler.source, StateT.run]
  rw [HandlerComponents.hash_denote, HashDispatch.denote]
  dsimp only
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  rfl

-- Malformed signing replies retain the original request and public config,
-- and the actual hash/sign shared store only changes its malformed flag.
example : (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
    (request (.sign 7) [2, 2] [[], [1, 3]], (1, 2), [], [(1, 0)], [8], false, false) =
    pure (scalarTag true ((7, [2, 2], [[], [1, 3]]), (0, [])), (1, 2),
      [], [(1, 0)], [8], true, false) := by
  rw [Handler.code_denote]
  simp only [request, Handler.source, StateT.run]
  rw [HandlerComponents.signing_denote, SigningDispatch.denote]
  simp only [List.cons_ne_nil, ite_false, map_pure]
  rfl

-- The random tag restores the exact dependent Fin reply. This checks all
-- runtime arities, even when the request carries malformed group arguments.
example (n : Nat) : (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
    (request (.random n) [2] [[], [1]], (1, 2), [], [], [], false, true) =
    (fun r : Fin (n + 1) =>
      ((⟨request (.random n) [2] [[], [1]], ⟨r, fun _ => []⟩⟩ : SourceIndex F F Nat),
        (1, 2), [], [], [], true, true)) <$>
      (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  rw [Handler.code_denote]
  simp only [request, Handler.source, StateT.run]
  rw [HandlerComponents.random_denote, Random.denote]
  simp only [Functor.map_map]
  apply congrArg (fun f => f <$> (unifSpec.query n : ProbComp (Fin (n + 1))))
  funext r
  have h : Fin.ofNat (n + 1) r.val = r := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt r.isLt
  simp only [h]
  rfl

-- The second request depends on the commitment returned by signing. It uses
-- the same cache, sees the programmed challenge, and preserves both histories.
example (hs : sampler.denote () = pure (2 : F)) : (do
    let p ← (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
      (request (.sign 7) [] [], (1, 2), [], [(1, 0), (0, 1)], [], false, false)
    (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
      (request (.hash 7) [(p.1.2.groups ()).headD 0] [[2, 5]], p.2)) =
    pure (scalarTag false ((7, [5], [[2, 5]]), (2, [])), (1, 2),
      [((7, 5), (2, false, 0, 0))], [(1, 0), (0, 1), (2, 5)], [7], false, false) := by
  have first : (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
      (request (.sign 7) [] [], (1, 2), [], [(1, 0), (0, 1)], [], false, false) =
      pure (scalarTag true ((7, [], []), (2, [5])), (1, 2),
        [((7, 5), (2, false, 0, 0))], [(1, 0), (0, 1), (2, 5)], [7], false, false) := by
    rw [Handler.code_denote]
    simp only [request, Handler.source, StateT.run]
    rw [HandlerComponents.signing_denote, SigningDispatch.denote]
    simp only [ite_true]
    rw [Signing.denote, hs]
    simp only [pure_bind, map_pure]
    rfl
  rw [first]
  dsimp only [sourceSpec, OracleSpec.toPFunctor, PFunctor.Idx]
  rw [pure_bind]
  change (Handler.code rep bd ports data cost primitive randomPorts sampler).denote
    (request (.hash 7) [5] [[2, 5]], (1, 2), [((7, 5), (2, false, 0, 0))],
      [(1, 0), (0, 1), (2, 5)], [7], false, false) = _
  rw [Handler.code_denote]
  simp only [request, Handler.source, StateT.run]
  rw [HandlerComponents.hash_denote, HashDispatch.denote]
  dsimp only
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  rfl

variable [C.HasOption] [Q.HasOption] [OptionCode (Q := Q)]
  [DecidableEq (SourceRequest F F Nat)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

-- Terminal readout at zero fuel is a result, and retains the entire store.
example (input output : F) (hv : R.machine.view (R.machine.init input) = .inl output)
    (saved : (storeTy.Value (cryptoBase F F F Nat Nat))) :
    (Handler.caller rep bd ports data cost primitive randomPorts sampler R 0).denote (input, saved) =
      pure (some output, saved) := by
  rw [Handler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]

-- An unanswered query at zero fuel remains an observable cutoff.
example (input : F) (q : SourceRequest F F Nat) (next : (sourceSpec F F Nat).Range q → R.machine.State)
    (hv : R.machine.view (R.machine.init input) = .inr ⟨q, next⟩)
    (saved : (storeTy.Value (cryptoBase F F F Nat Nat))) :
    (Handler.caller rep bd ports data cost primitive randomPorts sampler R 0).denote (input, saved) =
      pure (none, saved) := by
  rw [Handler.caller_denote]
  simp [runWithInput, runWith, unroll, hv]

end Native

-- Primitive-derived component budgets must stay available for infinite
-- message types and must not turn completed native programs into premises.
open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let publicBounds := #[``HandlerComponents.random_bound, ``HandlerComponents.signing_bound,
    ``HandlerComponents.hash_bound]
  for name in publicBounds ++ #[``HashDispatch.histories_run,
      ``HandlerComponents.store_mono, ``HandlerComponents.read_state,
      ``HandlerComponents.random_input, ``HandlerComponents.signing_input, ``HandlerComponents.hash_input,
      ``HandlerComponents.config_size, ``HandlerComponents.store_size, ``HandlerComponents.args_size,
      ``HandlerComponents.input_size, ``HandlerComponents.output_size,
      ``HandlerComponents.randomInput_cost, ``HandlerComponents.hashInput_cost, ``HandlerComponents.signingInput_cost,
      ``HandlerComponents.groupOutput_cost, ``HandlerComponents.hashOutput_cost,
      ``HandlerComponents.random_bound_of_native, ``HandlerComponents.signing_bound_of_native,
      ``HandlerComponents.hash_bound_of_native] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in publicBounds do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``HandlerComponents.random, ``HandlerComponents.hash, ``HandlerComponents.signing,
            ``HandlerComponents.localCode, ``Random.code, ``HashDispatch.code, ``SigningDispatch.code,
            ``Signing.code, ``Hash.code, ``Read.code, `Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate, `Signatures.Runtime.GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes completed component efficiency or restricts attacker implementation"
        if name == ``HandlerComponents.random_bound &&
            (type.find? (fun e => e.isConstOf ``Bounds)).isSome then
          throwError "{name}: assumes a completed sampler budget"

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``decode_encodeRequest, ``encode_decodeRequest, ``randomTag_fin,
      ``HandlerComponents.random_denote, ``HandlerComponents.hash_denote, ``HandlerComponents.signing_denote,
      ``HandlerComponents.localCode_description, ``Handler.random_denote, ``Handler.group_denote,
      ``Handler.code_denote, ``Handler.code_executed_run, ``Handler.executed_erase, ``Handler.caller_denote,
      ``Handler.source_refines, ``Handler.code_source, ``Handler.caller_source,
      ``Handler.random_description, ``Handler.group_description, ``Handler.code_description, ``Handler.caller_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[`Signatures.Runtime.AGM.SourceCertificate,
            `Signatures.Runtime.Schnorr.SourceCertificate, ``Bounds, `Signatures.Runtime.GeneralCaller.Budget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: unexpected arithmetic attacker restriction or assumed whole-program budget"

end SignaturesTest.BackendSchnorrAGMHandler
