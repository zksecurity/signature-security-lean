import Signatures.Runtime.BackendCoronInterface

/-! The complete native oracle dispatcher for a general Coron caller. It
decodes a request, selects randomness/hash/sign, runs the existing native reply
routine, and tags its response with the original request. The source-law theorem
preserves the joint response/store distribution; it does not transfer old costs. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))

def group (qS : Nat) (signing : Bool) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod bd.idx (rep.ty (machineStore qS))) :=
  .seq (Language.withContext (rep.ty (machineStore qS)) (Q.identity (rep.ty message))
    (backendReply rep data samplingCode cost primitive qS signing))
    (.first (rep.ty (machineStore qS)) (.atomic (Q.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing))))

def random (qS : Nat) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod bd.idx (rep.ty (machineStore qS))) :=
  .seq (.first (rep.ty (machineStore qS)) sampler.code)
    (.first (rep.ty (machineStore qS)) (.atomic ports.randomTag))

def inner (qS : Nat) :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod bd.idx (rep.ty (machineStore qS))) :=
  .seq (.atomic (QD.distribute (rep.ty (boundedNat randomBound)) (rep.ty message) (rep.ty (machineStore qS))))
    (.branch (random rep bd ports sampler qS) (group rep bd ports data samplingCode cost primitive qS false))

def dispatch (qS : Nat) :
    Code Q unifSpec iface (StepClass.HasProd.prod (generalPositions rep randomBound) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod bd.idx (rep.ty (machineStore qS))) :=
  .seq (.atomic (QD.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message))
    (rep.ty message) (rep.ty (machineStore qS))))
    (.branch (inner rep bd ports sampler data samplingCode cost primitive qS)
      (group rep bd ports data samplingCode cost primitive qS true))

def code (qS : Nat) :
    Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod bd.idx (rep.ty (machineStore qS))) :=
  .seq (.first (rep.ty (machineStore qS)) (.atomic ports.request))
    (dispatch rep bd ports sampler data samplingCode cost primitive qS)

section Semantics

-- The request ranges use definitionally equal dependent-sum aliases.
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

omit QD in
theorem group_denote (qS : Nat) (signing : Bool) (m : M)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (group rep bd ports data samplingCode cost primitive qS signing).denote (m, saved) =
      (fun p => (tagGroup (G₁ := G₁) signing (m, p.1), p.2)) <$>
        (backendReply rep data samplingCode cost primitive qS signing).denote (m, saved) := by
  simp only [group, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

omit [Q.HasCategory] QP QS QD [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M] in
theorem random_denote (qS : Nat) (n : Fin (randomBound + 1))
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (random rep bd ports sampler qS).denote (n, saved) =
      (fun reply => (tagRandom (M := M) (G₁ := G₁) ⟨n, reply⟩, saved)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  simp only [random, Code.denote, sampler.denote, map_pure, bind_pure_comp, Functor.map_map]

theorem code_random_denote (qS : Nat) (n : Fin (randomBound + 1))
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).denote (.inl (.inl n), saved) =
      (fun reply => (tagRandom (M := M) (G₁ := G₁) ⟨n, reply⟩, saved)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind]
  exact random_denote rep bd ports sampler qS n saved

theorem code_hash_denote (qS : Nat) (m : M)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).denote (.inl (.inr m), saved) =
      (fun p => (tagGroup (G₁ := G₁) false (m, p.1), p.2)) <$>
        (backendReply rep data samplingCode cost primitive qS false).denote (m, saved) := by
  simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind]
  exact group_denote rep bd ports data samplingCode cost primitive qS false m saved

theorem code_sign_denote (qS : Nat) (m : M)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).denote (.inr m, saved) =
      (fun p => (tagGroup (G₁ := G₁) true (m, p.1), p.2)) <$>
        (backendReply rep data samplingCode cost primitive qS true).denote (m, saved) := by
  simp only [code, dispatch, Code.denote, map_pure, pure_bind]
  exact group_denote rep bd ports data samplingCode cost primitive qS true m saved

theorem code_denote (sampling : Machine.SamplingCosts) (qS : Nat) (i : GeneralRequest M randomBound)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).denote (i, saved) =
      (fun p => ((⟨i, p.1.value⟩ : GeneralIndex M G₁ randomBound), p.2)) <$>
        ((generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound i).run saved) := by
  obtain ⟨⟨g, X, h⟩, scalars, coins, signed⟩ := saved
  let state : CacheState F M qS := ⟨scalars, coins, signed⟩
  rcases i with (n | m) | m
  · rw [code_random_denote]
    have he := machineHandler_erase (G₂ := G₂) cost sampling g X h qS randomBound (.random n) () state
    have ht := congrArg (fun c : ProbComp (Fin (n.val + 1) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) =>
      (fun p => ((⟨Sum.inl (Sum.inl n), p.1⟩ : GeneralIndex M G₁ randomBound), p.2)) <$> c) he
    simp only [Coron.handler, StateT.run, Functor.map_map, tagRandom, generalHandler, machineState, state] at ht ⊢
    exact ht
  · rw [code_hash_denote]
    have hb := backendReply_denote rep data samplingCode cost primitive sampling g X h qS false m state
    erw [hb]
    have he := machineHandler_erase (G₂ := G₂) cost sampling g X h qS randomBound .hash m state
    have ht := congrArg (fun c : ProbComp (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) =>
      (fun p => ((⟨Sum.inl (Sum.inr m), p.1⟩ : GeneralIndex M G₁ randomBound), p.2)) <$> c) he
    simp only [Coron.handler, StateT.run, Functor.map_map, tagGroup, Bool.false_eq_true, ite_false,
      generalHandler, machineState, state] at ht ⊢
    exact ht
  · rw [code_sign_denote]
    have hb := backendReply_denote rep data samplingCode cost primitive sampling g X h qS true m state
    erw [hb]
    have he := machineHandler_erase (G₂ := G₂) cost sampling g X h qS randomBound .sign m state
    have ht := congrArg (fun c : ProbComp (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) =>
      (fun p => ((⟨Sum.inr m, p.1⟩ : GeneralIndex M G₁ randomBound), p.2)) <$> c) he
    simp only [Coron.handler, StateT.run, Functor.map_map, tagGroup, ite_true,
      generalHandler, machineState, state] at ht ⊢
    exact ht

end Semantics

end Signatures.Runtime.Coron.NativeHandler
