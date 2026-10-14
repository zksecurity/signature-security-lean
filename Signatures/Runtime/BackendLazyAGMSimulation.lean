import Signatures.Runtime.BackendLazyAGMReply
import Signatures.Runtime.LazyAGMExecution

/-! Adaptive semantics of the actual native lazy AGM reply routines. These
handlers execute compiled reply code and the primitive randomness implementation.
Their equality to the flattened source interpreter preserves all adaptive paths,
including private random choices, repeated replies, and the shared private cache.
-/

open OracleComp OracleSpec PFunctor Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M α : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)

omit [SampleableType F] in
theorem backendReply_state {value config : Ty CryptoAtom}
    [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (response : Expr CryptoOp [value, config] point₁)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (signing : Bool) (m : M) (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (state : State M (value.Value (cryptoBase F G₁ G₂ M M)) G₁)
    (p : M → Prop) (hi : state.Messages p) (hm : p m)
    (out : Run (G₁ × (storeTy value config).Value (cryptoBase F G₁ G₂ M M)))
    (hout : out ∈ support ((backendReply rep data cost primitive sampler fallback response signing).run
      control queryCost (m, cfg, state))) :
    out.value.2.1 = cfg ∧ State.Messages p out.value.2.2 ∧
      out.value.2.2.1.length ≤ state.1.length + 1 ∧
      out.value.2.2.2.1.length + out.value.2.2.2.2.length = state.2.1.length + state.2.2.length + 1 := by
  have hv := Code.value_mem_denote control queryCost
    (backendReply rep data cost primitive sampler fallback response signing) (m, cfg, state) out hout
  rw [backendReply_denote rep data cost primitive sampler fallback response hsample] at hv
  simp only [support_map, Set.mem_image] at hv
  obtain ⟨r, hr, he⟩ := hv
  rw [← he]
  let f := fun v => response.denote (arithmetic F G₁ G₂ M M cost) (v, cfg, ())
  have hlocal : (f r.1, r.2, record signing m (f r.1) state.2) ∈
      support ((listReply signing f m).run state) := by
    simp only [listReply, StateT.run, support_map, Set.mem_image]
    exact ⟨r, hr, rfl⟩
  have hmessages := listReply_messages signing f m p state hi hm _ hlocal
  have hgrowth := listReply_growth signing f m state _ hlocal
  exact ⟨rfl, hmessages, hgrowth.1, hgrowth.2⟩

noncomputable def backendGoodOracle (g X : G₁) :
    QueryImpl (advSpec M M G₁) (StateT (State M F G₁) ProbComp) := fun q => match q with
  | .inl (.inl n) => fun state => (fun r => (r, state)) <$> (samplingCode.uniform n).denote ()
  | .inl (.inr m) => fun state => (fun p => (p.1, p.2.2)) <$>
      (backendGoodReply rep data cost primitive samplingCode false).denote (m, (g, X), state)
  | .inr m => fun state => (fun p => (p.1, p.2.2)) <$>
      (backendGoodReply rep data cost primitive samplingCode true).denote (m, (g, X), state)

noncomputable def backendBadOracle (g X : G₁) (kappa : F) :
    QueryImpl (advSpec M M G₁) (StateT (State M (F × F) G₁) ProbComp) := fun q => match q with
  | .inl (.inl n) => fun state => (fun r => (r, state)) <$> (samplingCode.uniform n).denote ()
  | .inl (.inr m) => fun state => (fun p => (p.1, p.2.2)) <$>
      (backendBadReply rep data cost primitive samplingCode false).denote (m, (kappa, g, X), state)
  | .inr m => fun state => (fun p => (p.1, p.2.2)) <$>
      (backendBadReply rep data cost primitive samplingCode true).denote (m, (kappa, g, X), state)

theorem backendGoodOracle_eq (g X : G₁) :
    backendGoodOracle rep data cost primitive samplingCode g X =
      listOracle (fun rho : F => rho • g) (fun rho => rho • X) := by
  funext q state
  rcases state with ⟨cache, tr⟩
  rcases q with ((n | m) | m)
  · simp [backendGoodOracle, listOracle, samplingCode.uniform_denote]
  · simp only [backendGoodOracle]
    rw [backendGoodReply_denote]
    simp only [Bool.false_eq_true, ite_false, Functor.map_map, listOracle, listReply, StateT.run]
  · simp only [backendGoodOracle]
    rw [backendGoodReply_denote]
    simp only [ite_true, Functor.map_map, listOracle, listReply, StateT.run]

theorem backendBadOracle_eq (g X : G₁) (kappa : F) :
    backendBadOracle rep data cost primitive samplingCode g X kappa =
      listOracle (fun masks : F × F => masks.1 • X + masks.2 • g)
        (fun masks => kappa • (masks.1 • X + masks.2 • g)) := by
  funext q state
  rcases state with ⟨cache, tr⟩
  rcases q with ((n | m) | m)
  · simp [backendBadOracle, listOracle, samplingCode.uniform_denote]
  · simp only [backendBadOracle]
    rw [backendBadReply_denote]
    simp only [Bool.false_eq_true, ite_false, Functor.map_map, listOracle, listReply, StateT.run]
  · simp only [backendBadOracle]
    rw [backendBadReply_denote]
    simp only [ite_true, Functor.map_map, listOracle, listReply, StateT.run]

theorem backendGoodSimulation (g X : G₁) (oa : OracleComp (advSpec M M G₁) α)
    (cache : List (M × F)) (tr : Transcript M M G₁) :
    observe <$> (simulateQ (backendGoodOracle rep data cost primitive samplingCode g X) oa).run (cache, tr) =
      (simulateQ privateListOracle
        ((simulateQ (privateOracle (fun rho : F => rho • g) (fun rho => rho • X)) oa).run
          (chronological tr))).run cache := by
  rw [backendGoodOracle_eq]
  exact listSimulation _ _ oa cache tr

theorem backendBadSimulation (g X : G₁) (kappa : F) (oa : OracleComp (advSpec M M G₁) α)
    (cache : List (M × (F × F))) (tr : Transcript M M G₁) :
    observe <$> (simulateQ (backendBadOracle rep data cost primitive samplingCode g X kappa) oa).run (cache, tr) =
      (simulateQ privateListOracle
        ((simulateQ (privateOracle (fun masks : F × F => masks.1 • X + masks.2 • g)
          (fun masks => kappa • (masks.1 • X + masks.2 • g))) oa).run (chronological tr))).run cache := by
  rw [backendBadOracle_eq]
  exact listSimulation _ _ oa cache tr

end Signatures.Runtime.LazyAGM
