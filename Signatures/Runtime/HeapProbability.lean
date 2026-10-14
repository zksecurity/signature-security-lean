import Signatures.Runtime.HeapPackage
import Signatures.Runtime.MachineSampling
import Signatures.Runtime.ProgramSimulation
import Signatures.Runtime.MachineProbability

/-! Exact probability laws connecting the sampling-request tree to the
existing fair-bit machine semantics. Decoders here are proof observations,
not extra operations in the executable program. -/

namespace Signatures.Runtime.HeapMachine

open OracleComp HeapBits SharedHeap PrimeFieldCircuit WeierstrassCurve

private theorem stateMap_apply {S A B : Type} (f : A → B) (code : StateT S PMF A) (s : S) :
    (f <$> code) s = (fun out => (f out.1, out.2)) <$> code s := StateT.run_map f code s

noncomputable abbrev fairBits : QueryImpl BitRejection.bitSpec PMF :=
  fun _ => PMF.uniformOfFintype Bool

/-- Mathematical observation of a returned scalar encoding. It is not an
extra online operation or a claim about the cost of exporting the heap. -/
def scalarValue (r : Nat) (out : HeapExpression.Result) : ZMod r :=
  match out with
  | none => 0
  | some (root, store) => match (readWord store.memory root).value with
    | none => 0
    | some bits => exponent bits

noncomputable def markedHom {r : Nat} [NeZero r] (w k : Nat) (S : Type) :
    StateT S (OracleComp (MachineSampling.spec (ZMod r))) →ᵐ StateT (S × Bool) PMF :=
  Simulation.flatten ∘ₘ StateT.mapHom (simulateQ' (MarkedProbability.stateImpl (MachineSampling.real r w k)))

private theorem finEquiv_ofNat (r n : Nat) [NeZero r] :
    ZMod.finEquiv r (Fin.ofNat r n) = (n : ZMod r) := by
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ r => rfl

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)

theorem effects_probability (k : Nat) (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom)
    {a b} (cmd : Machine.Effect storage a b) (arg : a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) :
    markedHom w k _ (MachineSampling.effects (ZMod r) H₁ H₂ K M sampling storage cmd arg) =
      StateT.mapHom (simulateQ' fairBits) (semantics H₁ H₂ (w := w) k sampling storage cmd arg) := by
  funext state
  cases cmd with
  | scalar =>
    simp [markedHom, Simulation.flatten, StateT.mapHom, MachineSampling.effects,
      semantics, MachineSampling.real, MarkedProbability.stateImpl, PaddedSampling.decoded,
      StateT.run, StateT.mk, stateMap_apply, PMF.monad_map_eq_map, PMF.map_comp,
      Function.comp_def]
    congr 1
    funext out
    exact congrArg (fun x => (Run.mk x sampling.scalar, state.1, state.2 || out.value.2))
      (finEquiv_ofNat r (exponent out.value.1))
  | uniform n =>
    simp [markedHom, Simulation.flatten, StateT.mapHom, MachineSampling.effects,
      semantics, MachineSampling.real, MarkedProbability.stateImpl, PaddedSampling.decoded,
      StateT.run, StateT.mk, stateMap_apply, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  | read =>
    change (fun out => (out.1.1, out.1.2, out.2)) <$>
      (PMF.pure ((Run.mk state.1 1, state.1), state.2)) = PMF.pure (Run.mk state.1 1, state)
    exact PMF.pure_map _ _
  | write =>
    change (fun out => (out.1.1, out.1.2, out.2)) <$>
      (PMF.pure ((Run.mk () 1, arg), state.2)) = PMF.pure (Run.mk () 1, arg, state.2)
    exact PMF.pure_map _ _

variable [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]

omit [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂] in
theorem scalarValue_eq (encodeK : K → BitVec w) (encodeM : M → BitVec w)
    {cap n : Nat} {heap : List Node} {x : ZMod r} {out : Run HeapExpression.Result}
    (hr : r ≤ 2^w)
    (h : HeapExpression.ResultSpec (t := scalar) w cap (atomRep H₁ H₂ encodeK encodeM) heap n x out) :
    scalarValue r out.value = x := by
  obtain ⟨extra, root, store, hv, hs, _, hx, _⟩ := h
  have hl := loadPorts_value H₁ H₂ encodeK encodeM (.atom .scalar) root x hx
  change (readWord (tape (heap ++ extra)) root).value = some (natBits w x.val) at hl
  rw [hv, scalarValue, hs.2, hl]
  change (exponent (natBits w x.val) : ZMod r) = x
  rw [HeapLoop.exponent_natBits _ _ ((ZMod.val_lt x).trans_le hr)]
  exact ZMod.natCast_zmod_val x

theorem body_probability (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {storage Γ a} (code : Program CryptoOp (Machine.Effect storage) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (state) :
    (MarkedProbability.simulate (MachineSampling.real r w k)
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost)
        (MachineSampling.effects (ZMod r) H₁ H₂ K M sampling storage) env).run state)).map
          (fun out => (out.1.1, out.1.2, out.2)) =
      simulateQ fairBits ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost)
        (semantics H₁ H₂ (w := w) k sampling storage) env).run (state, false)) := by
  have h := code.run_mmap (markedHom w k _) (arithmetic (ZMod r) H₁ H₂ K M cost)
    (MachineSampling.effects (ZMod r) H₁ H₂ K M sampling storage) env
  simp_rw [effects_probability H₁ H₂ k sampling storage] at h
  rw [← code.run_mmap (StateT.mapHom (simulateQ' fairBits))] at h
  have h := congrArg (fun x => x.run (state, false)) h
  change (fun out => (out.1.1, out.1.2, out.2)) <$>
    ((simulateQ (MarkedProbability.stateImpl (MachineSampling.real r w k))
      ((code.run (arithmetic (ZMod r) H₁ H₂ K M cost)
        (MachineSampling.effects (ZMod r) H₁ H₂ K M sampling storage) env).run state)).run false) = _ at h
  rw [MarkedProbability.simulate_state_false] at h
  exact h

theorem code_probability (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) :
    MarkedProbability.simulate (MachineSampling.real r w k) (MachineSampling.tree cost sampling code env) =
      simulateQ fairBits (codeSemantics H₁ H₂ (w := w) k cost sampling code env) := by
  let initial := code.init.run (arithmetic (ZMod r) H₁ H₂ K M cost) env
  have h := body_probability H₁ H₂ (w := w) k cost sampling code.body env initial.value
  have h := congrArg (fun p => p.map (fun out =>
    (Run.mk out.1.value (initial.steps+out.1.steps+2), out.2.2))) h
  simpa only [MachineSampling.tree, codeSemantics, bind_pure_comp, MarkedProbability.simulate_map,
    simulateQ_map, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, initial] using h

theorem package_probability (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) :
    MarkedProbability.simulate (MachineSampling.real r w k) (MachineSampling.packageTree cost sampling pack env) =
      simulateQ fairBits (packageSemantics H₁ H₂ (w := w) k cost sampling pack env) := by
  simp only [MachineSampling.packageTree, packageSemantics, MarkedProbability.simulate_map,
    code_probability H₁ H₂, simulateQ_map, PMF.monad_map_eq_map]

open scoped ENNReal

/-- The complete marked package loses at most one rejection-error allowance
per source-budget unit, relative to the original ideal machine execution. -/
theorem package_error [SampleableType (ZMod r)]
    (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) (B : Nat) (hB : B ≤ w)
    (hr : r ≤ 2^w) (hsampling : ∀ n, n < 2^(sampling.uniform n))
    (hb : ∀ out ∈ support (pack.run cost sampling env), out.steps ≤ B) :
    MarkedProbability.GoodLe
      (simulateQ fairBits (packageSemantics H₁ H₂ (w := w) k cost sampling pack env))
      (simulateQ MachineSampling.uniformNaturals (pack.run cost sampling env)) ∧
    MarkedProbability.bad
      (simulateQ fairBits (packageSemantics H₁ H₂ (w := w) k cost sampling pack env)) ≤
        B * (1/2 : ℝ≥0∞)^k := by
  have h := MachineSampling.probability r w k sampling B hB hr hsampling
    (MachineSampling.packageTree cost sampling pack env)
    (MachineSampling.packageTree_bound cost sampling pack env B hb)
  rwa [package_probability H₁ H₂, MachineSampling.package_ideal_probability] at h

end Signatures.Runtime.HeapMachine
