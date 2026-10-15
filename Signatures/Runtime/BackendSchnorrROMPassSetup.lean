import Signatures.Runtime.BackendSchnorrROMPassLocalCost
import Signatures.Runtime.BackendSchnorrROMPassSize
import Signatures.Runtime.BackendSchnorrROMPassPorts
import Signatures.Runtime.BackendDispatchBudget

/-! Initialization pays for both empty caches, the retained configuration/tape
and the actual caller-input conversion. Initial tape capacities may be nonzero,
so the same theorem covers initial execution and replay. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem setup_bound
    (width tapeWidth mc lc sc rc initialSavedCap drawCap fuel routeWidth frame inputTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hw : (6 * (sc + rc) + 3) * tapeWidth ≤ width)
    (hframe : (12 * (mc + lc) + 40) * width ≤ frame) (hr : routeWidth ≤ frame)
    (hm : fuel ≤ mc) (hl : fuel ≤ lc) (hs : initialSavedCap + fuel * drawCap ≤ sc)
    (hconvert : ∀ pk, Q.size (rep.ty point₁) pk ≤ width →
      Q.size bd.input pk ≤ routeWidth ∧ Q.cost boundary.input pk ≤ inputTime) :
    Bounds control queryCost (setup (iface := iface) rep bd boundary data cost primitive)
      (fun p => ConfigBound (Q := Q) rep width p.2 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap rc p.1)
      (fun p => Q.size bd.input p.1 ≤ routeWidth ∧
        NativeHandler.ReservedState (Q := Q) rep width tapeWidth mc lc sc rc drawCap fuel p.2)
      (inputTime + 1032 * overhead (8192 * frame)) := by
  let fee := overhead (8192 * frame)
  let inv := NativeHandler.ReservedState (Q := Q) rep width tapeWidth mc lc sc rc drawCap fuel
  let pre := fun p : inputTy.Value (cryptoBase F G₁ G₂ K M) =>
    ConfigBound (Q := Q) rep width p.2 ∧ NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap rc p.1
  let middle := fun p : (withStore point₁).Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty point₁) p.1 ≤ width ∧ inv p.2
  let post := fun p : G₁ × Shared.Store F G₁ M => Q.size bd.input p.1 ≤ routeWidth ∧ inv p.2
  have hwf : width ≤ frame := by nlinarith only [hframe, Nat.zero_le ((mc + lc) * width)]
  have hstore (saved) (hi : inv saved) : Q.size (rep.ty storeTy) saved ≤ frame := by
    have h := store_size rep sizes lists width tapeWidth mc lc sc rc hh ht hw saved hi.store
    nlinarith only [h, hframe]
  have hin (p) (hi : pre p) : Q.size (rep.ty inputTy) p ≤ frame := by
    have hc := config_size rep sizes width hh p.2 hi.1
    have htw := NativeUniform.state_size rep sizes lists tapeWidth initialSavedCap rc ht p.1 hi.2
    have hw0 : (6 * (initialSavedCap + rc) + 3) * tapeWidth ≤ width :=
      (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
    have hp := sizes.prod_le (rep.ty NativeUniform.stateTy) (rep.ty configTy) p
    change Q.size (rep.ty inputTy) p ≤ _ at hp
    nlinarith only [hc, htw, hw0, hp, hh, hframe, Nat.zero_le ((mc + lc) * width)]
  have hmid (p) (hi : middle p) : Q.size (rep.ty (withStore point₁)) p ≤ frame := by
    have h := input_size rep sizes lists point₁ width width tapeWidth mc lc sc rc hh ht (by omega) hw p
      ⟨hi.1, hi.2.store⟩
    nlinarith only [h, hframe]
  have ha : Bounds control queryCost (.atomic (iface := iface)
      (localCode rep data cost primitive initialExpression)) pre middle (1029 * fee) := by
    apply Bounds.atomic
    intro p hp
    have hout : middle (p.2.2, ((p.2, [], []), p.1)) :=
      ⟨hp.1.2, initial_reserved rep width tapeWidth mc lc sc rc initialSavedCap drawCap fuel
        p.2.1 p.2.2 p.1 hp.1 hp.2 hm hl hs⟩
    have hi := hin p hp
    have ho := hmid _ hout
    have hc := (initialExpression_cost rep data cost primitive sizes lists laws dataLaws mono p frame
      (hh.trans hwf) (hu.trans hwf) hi).2
    have hm' := mono (show 256 * frame ≤ 8192 * frame by omega)
    have hf := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty inputTy) p + Q.size (rep.ty (withStore point₁)) (p.2.2, ((p.2, [], []), p.1)) ≤
        8192 * frame by omega))
    refine ⟨hout, ?_⟩
    change Q.cost (localCode rep data cost primitive initialExpression) p +
      control.localCall (Q.size (rep.ty inputTy) p)
        (Q.size (rep.ty (withStore point₁)) (p.2.2, ((p.2, [], []), p.1))) ≤ 1029 * fee
    dsimp only [fee]
    omega
  have hb := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty storeTy)
    boundary.input (fun pk => Q.size (rep.ty point₁) pk ≤ width)
    (fun pk => Q.size bd.input pk ≤ routeWidth) inv frame inputTime
    (fun _ h => h.trans hwf) hstore
    (fun pk h => ⟨(hconvert pk h).1, (hconvert pk h).1.trans hr, (hconvert pk h).2⟩)
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre middle post frame
    (1029 * fee) (inputTime + 2 * overhead (32 * frame)) hin hmid ha hb
  apply Bounds.time_mono control queryCost hall
  have hf := mono (show 32 * frame ≤ 8192 * frame by omega)
  dsimp only [fee]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativePass
