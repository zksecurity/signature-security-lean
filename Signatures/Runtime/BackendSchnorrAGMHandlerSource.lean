import Signatures.Runtime.BackendSchnorrAGMHandler
import Signatures.Runtime.GeneralCallerRefinement

/-! Exact adaptive correspondence between the installed native Schnorr handler
and the established finite-list reduction. The caller is a general quantitative
realization; it is not required to be an arithmetic-language program. -/

open OracleComp OracleSpec PFunctor AlgebraicGroupModel.Interaction Schnorr.AGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (hsample : sampler.denote () = ($ᵗ F : ProbComp F))

include hsample

theorem source_refines (g pk : G₁) (q : SourceRequest F G₁ M) :
    StateRefines (fun s : State F G₁ M => ((g, pk), encodeState s))
      (handler g pk q) (source rep data cost primitive randomPorts sampler q) := by
  intro s
  rcases q with ⟨⟨q, groups⟩, rows⟩
  cases q with
  | random n =>
      simp only [source, StateT.run]
      rw [HandlerComponents.random_denote rep data cost primitive randomPorts]
      rw [Random.source rep data cost primitive randomPorts g pk s n (groups ()) (rows ())]
      simp only [Functor.map_map]
      apply congrArg (fun f => f <$> (handler g pk (request (.random n) (groups ()) (rows ()))).run s)
      funext p
      rcases p with ⟨⟨r, replyGroups⟩, t⟩
      have h : Fin.ofNat (n + 1) r.val = r := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt r.isLt
      simp only [h]
  | hash m =>
      simp only [source, StateT.run]
      rw [HandlerComponents.hash_denote rep data cost primitive sampler]
      have h := congrArg (Functor.map (fun p : Message F (Group G₁) × EncodedState F G₁ M =>
        (p.1, (g, pk), p.2)))
        (HashDispatch.source rep data cost primitive sampler hsample g pk s m (groups ()) (rows ()))
      dsimp only [OracleSpec.Range, explainedSpec, Reply] at h ⊢
      simp only [Functor.map_map] at h ⊢
      exact h.symm
  | sign m =>
      simp only [source, StateT.run]
      rw [HandlerComponents.signing_denote rep data cost primitive sampler]
      have h := congrArg (Functor.map (fun p : Message F (Group G₁) × EncodedState F G₁ M =>
        (p.1, (g, pk), p.2)))
        (SigningDispatch.source rep data cost primitive sampler hsample g pk s m (groups ()) (rows ()))
      dsimp only [OracleSpec.Range, explainedSpec, Reply] at h ⊢
      simp only [Functor.map_map] at h ⊢
      exact h.symm

variable [QD : Q.IsDistributive]
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)

theorem code_source (g pk : G₁) (q : SourceRequest F G₁ M) (s : State F G₁ M) :
    (code rep bd ports data cost primitive randomPorts sampler).denote (q, (g, pk), encodeState s) =
      (fun p => ((⟨q, p.1⟩ : SourceIndex F G₁ M), (g, pk), encodeState p.2)) <$>
        (handler g pk q).run s := by
  rw [code_denote, ← source_refines rep data cost primitive randomPorts sampler hsample g pk q s]
  simp only [Functor.map_map]
  rfl

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  [DecidableEq (SourceRequest F G₁ M)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem caller_source (fuel : Nat) (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input)
    (g pk : G₁) (s : State F G₁ M) :
    (caller rep bd ports data cost primitive randomPorts sampler R fuel).denote (input, (g, pk), encodeState s) =
      (fun p => (some p.1, (g, pk), encodeState p.2)) <$>
        (simulateQ (handler g pk) (program input)).run s := by
  rw [caller_denote, hprogram.simulateQ_run_eq]
  have h := GeneralCaller.simulateQ_refines (fun s : State F G₁ M => ((g, pk), encodeState s))
    (handler g pk) (source rep data cost primitive randomPorts sampler)
    (source_refines rep data cost primitive randomPorts sampler hsample g pk) (program input) s
  change _ = (simulateQ (source rep data cost primitive randomPorts sampler) (program input)).run ((g, pk), encodeState s) at h
  simp only [StateT.run_map]
  rw [← h]
  simp only [Functor.map_map]

end Signatures.Runtime.SchnorrAGM.Native.Handler
