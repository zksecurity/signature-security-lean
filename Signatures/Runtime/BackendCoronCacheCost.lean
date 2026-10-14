import Signatures.Runtime.BackendCacheCost
import Signatures.Runtime.BackendCoronCost

/-! Complete native scalar/coin cache budgets for the cache calls inside
Coron's compiled reply procedure. Primitive sampling code is charged separately
from lookup, insertion, retained environments, and the unchanged ambient store.
Read/write, group arithmetic, and the surrounding reply assembly remain separate.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include localLaws dataLaws sizes lists mono routing

theorem scalarCache_bound (qS : Nat) (m : M) (state : CacheState F M qS)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (width comparisonTime sampleTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : state.Messages (fun m => Q.size (rep.ty message) m ≤ width))
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width) (hn : state.size ≤ cap)
    (hw : Q.size (rep.ty (machineStore qS)) saved ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (samplingCode.scalar.run control queryCost ()), z.steps ≤ sampleTime)
    (z : Run ((F × List (M × F)) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (cacheGet CryptoOp.messageEq .scalar)).run control queryCost ((m, 0, state.scalars, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1) z.value.1 ∧
      z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) + sampleTime +
        133 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  apply CacheCompiler.cacheGet_sampling_bound (key := message) (val := scalar)
    rep data (arithmetic F G₁ G₂ M M cost) primitive sizes lists localLaws dataLaws primitiveBound mono
    control queryCost routing (rep.ty (machineStore qS)) (MachineCompiler.effects rep data samplingCode (machineStore qS))
    CryptoOp.messageEq .scalar (fun _ _ => rfl) samplingCode.scalar rfl width cap comparisonTime sampleTime
    hh hu hb he ?_ (m, 0, state.scalars, ()) ?_ saved hw z hz
  · intro u _ r hr
    cases u
    exact ⟨hf r.value, hd r hr⟩
  · exact ⟨hm, hf 0, (fun p hp => ⟨hs.1 p hp, hf p.2⟩), (Nat.le_max_left _ _).trans hn⟩

theorem coinCache_bound (qS : Nat) (m : M) (state : CacheState F M qS)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (width comparisonTime sampleTime cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : state.Messages (fun m => Q.size (rep.ty message) m ≤ width))
    (hf : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width) (hn : state.size ≤ cap)
    (hw : Q.size (rep.ty (machineStore qS)) saved ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support ((samplingCode.uniform qS).run control queryCost ()), z.steps ≤ sampleTime)
    (z : Run ((Fin (qS + 1) × List (M × Fin (qS + 1))) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((MachineCompiler.program rep data samplingCode cost primitive (machineStore qS)
      (cacheGet CryptoOp.messageEq (.uniform qS))).run control queryCost ((m, 0, state.coins, ()), saved))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := boundedNat qS) width (cap + 1) z.value.1 ∧
      z.value.2 = saved ∧
      z.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) + sampleTime +
        133 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  apply CacheCompiler.cacheGet_sampling_bound (key := message) (val := boundedNat qS)
    rep data (arithmetic F G₁ G₂ M M cost) primitive sizes lists localLaws dataLaws primitiveBound mono
    control queryCost routing (rep.ty (machineStore qS)) (MachineCompiler.effects rep data samplingCode (machineStore qS))
    CryptoOp.messageEq (.uniform qS) (fun _ _ => rfl) (samplingCode.uniform qS) rfl width cap comparisonTime sampleTime
    hh hu hb he ?_ (m, 0, state.coins, ()) ?_ saved hw z hz
  · intro u _ r hr
    cases u
    exact ⟨hf r.value, hd r hr⟩
  · exact ⟨hm, hf 0, (fun p hp => ⟨hs.2.1 p hp, hf p.2⟩),
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans hn⟩

end Signatures.Runtime.Coron
