import Proofs.Runtime.BackendSchnorrROMPassSource
import Proofs.Runtime.BackendSchnorrROMSelectionBudget
import Proofs.Runtime.SchnorrRawForkMap

/-! Install the actual general pass and native selector in the retained-tape
controller. Measured resources establish exact source correspondence for both
runs, including the singleton representation and all rejection paths. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeROMFork

open BackendProgram RawTape NativeInterface NativeComponents

def output {F G₁ G₂ K M : Type}
    (result : Option (cachePassOutput.Value (cryptoBase F G₁ G₂ K M) ×
      cachePassOutput.Value (cryptoBase F G₁ G₂ K M))) :
    Unit ⊕ (NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M) ×
      NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) :=
  NativeFork.view (result.map (Prod.map (fun p => [p]) (fun p => [p])))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive] [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : NativePass.DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def code (fuel qH : Nat) : Code Q unifSpec iface (rep.ty configTy)
    (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair NativePass.outputTy NativePass.outputTy))) :=
  NativeFork.code rep data cost primitive (NativeSelection.selector rep data cost primitive qH)
    (NativePass.code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel) sampler

variable [SampleableType F] (sample : sampler.denote () = ($ᵗ F : ProbComp F))

include sample

theorem source_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel qH : Nat) (hfuel : bound.queries ≤ fuel)
    (attacker : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements attacker) (g pk : G₁) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).denote (g, pk) =
      output <$> simulateQ _root_.Schnorr.LazyROM.sample
        (RawTape.fork ((ListROM.pass (G₂ := G₂) (K := K) (attacker pk)).run ((g, pk), [], []))
          qH (selectPass PrimitiveCosts.unit qH)) := by
  let main := (ListROM.pass (G₂ := G₂) (K := K) (attacker pk)).run ((g, pk), [], [])
  have hpass (state : RawTape.State F) :
      (NativePass.code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel).denote
        (NativeUniform.encodeState state, g, pk) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ RawTape.oracle ((fun p => [p]) <$> main)).run state) := by
    rw [NativePass.source_of_resources rep bd boundary data cost primitive sampler sample ports uniform
      privatePorts R bound hrun fuel hfuel attacker implementation]
    simp only [Shared.tapeRun, NativeUniform.encodeState, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  have h := NativeFork.source rep data cost primitive (NativeSelection.selector rep data cost primitive qH)
    (NativePass.code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel) sampler
    qH ((fun p => [p]) <$> main) (NativeSelection.source qH) (g, pk)
    (NativeSelection.value_source qH) (hpass {})
    (fun first _ slot _ fresh => hpass (restart slot.val fresh first.2)) sample
  rw [RawTape.fork_map, simulateQ_map, Functor.map_map] at h
  have hselect : NativeSelection.source (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) qH ∘
      (fun p => [p]) = selectPass PrimitiveCosts.unit qH := by
    funext p
    exact NativeSelection.source_singleton PrimitiveCosts.unit qH p
  rw [hselect] at h
  exact h

theorem result_shape_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel qH : Nat) (hfuel : bound.queries ≤ fuel)
    (attacker : G₁ → OracleComp (sourceSpec F G₁ M) (M × G₁ × F))
    (implementation : R.machine.Implements attacker)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) (g pk : G₁)
    (z : Run (Unit ⊕ (NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M) ×
      NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M))))
    (hz : z ∈ support ((code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH).run
      control queryCost (g, pk))) :
    z.value = .inl () ∨ ∃ first second, z.value = .inr ([first], [second]) := by
  have hv := Code.value_mem_denote control queryCost
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel qH) (g, pk) z hz
  rw [source_of_resources rep bd boundary data cost primitive sampler ports uniform privatePorts R sample
    bound hrun fuel qH hfuel attacker implementation, support_map] at hv
  obtain ⟨result, _, he⟩ := hv
  cases result with
  | none => exact Or.inl he.symm
  | some pair => exact Or.inr ⟨pair.1, pair.2, he.symm⟩

end Signatures.Runtime.Schnorr.ListROM.NativeROMFork
