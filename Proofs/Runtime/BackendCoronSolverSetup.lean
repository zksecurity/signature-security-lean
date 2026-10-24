import Proofs.Runtime.BackendCoronSolverTerminal

/-! Challenge setup costs. The challenge is an actual encoded input, and all
projection, empty-cache construction, key conversion, and retained-store copying
costs are derived from local backend contracts. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem input_key_size (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁) :
    Q.size (rep.ty point₂) pk ≤ Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()) := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [inputTypes, LanguageRepresentation.env] at *
  grind only

include lists in
theorem initial_reserved (qS messageWidth width scalarWidth coinWidth groupWidth cap fuel : Nat)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (hcap : fuel ≤ cap) (g X h : G₁) :
    NativeHandler.ReservedState (Q := Q) rep qS messageWidth width cap fuel
      (machineState g X h (CacheState.empty : CacheState F M qS)) := by
  have hm := CacheState.messages_empty (F := F) (qS := qS) (fun m => Q.size (rep.ty message) m ≤ messageWidth)
  have hn : (CacheState.empty : CacheState F M qS).size ≤ cap := by simp [CacheState.empty, CacheState.size]
  have hs := machineState_encoded_size rep sizes lists qS g X h CacheState.empty
    messageWidth scalarWidth coinWidth groupWidth cap hm hf hc (hg _) (hg _) (hg _) hn
  refine ⟨hs.trans hw, hm, ?_⟩
  simpa [machineState, machineCaches, CacheState.empty, CacheState.size] using hcap

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (mono : Monotone overhead)
  (localLaws : LocalCostLaws Q overhead) (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

include lists mono localLaws dataLaws primitiveBound

theorem initial_cost (qS width : Nat) (hh : header ≤ width)
    (input : Env (cryptoBase F G₁ G₂ M M) inputTypes) (hi : Q.size (rep.env inputTypes) input ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (initial qS)) input ≤
      64 * overhead (32 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound (initial qS) input).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := @lists.nil_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [initial, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound, DataCostLaws.nilBound,
    inputTypes, LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

variable {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (boundary : DataPorts (Q := Q) rep bd)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

theorem setup_bound (qS inputWidth width routeWidth adapterTime : Nat)
    (hh : header ≤ width) (caps : PortCaps rep bd boundary inputWidth routeWidth adapterTime)
    (g : G₁) (g₂ : G₂) (X : G₁) (pk : G₂) (h : G₁)
    (hi : Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()) ≤ inputWidth)
    (hs : Q.size (rep.ty (machineStore qS)) (machineState g X h (CacheState.empty : CacheState F M qS)) ≤ width) :
    Bounds control queryCost (setup (iface := iface) rep bd boundary data cost primitive qS)
      (fun input => input = (g, g₂, X, pk, h, ()))
      (fun out => out = (pk, machineState g X h (CacheState.empty : CacheState F M qS)))
      (adapterTime + 70 * overhead (32 * (inputWidth + width + routeWidth))) := by
  let W := inputWidth + width + routeWidth
  let fee := overhead (32 * W)
  let saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M) :=
    machineState g X h (CacheState.empty : CacheState F M qS)
  let middle := fun p : G₂ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) => p = (pk, saved)
  have hk := (input_key_size rep sizes g g₂ X pk h).trans hi
  have hb := caps.key pk hk
  have hp := sizes.prod_le (rep.ty point₂) (rep.ty (machineStore qS)) (pk, saved)
  have ha : Bounds control queryCost
      (.atomic (iface := iface) (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (initial qS)))
      (fun input => input = (g, g₂, X, pk, h, ())) middle (65 * fee) := by
    apply Bounds.atomic
    intro input he
    subst input
    refine ⟨rfl, ?_⟩
    have ht := initial_cost rep sizes lists data cost primitive mono localLaws dataLaws primitiveBound
      qS W (by dsimp [W]; omega) (g, g₂, X, pk, h, ()) (hi.trans (by dsimp [W]; omega))
    have hc := routing.localCall (Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()))
      (Q.size (StepClass.HasProd.prod (rep.ty point₂) (rep.ty (machineStore qS))) (pk, saved))
    have hf := mono (show Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()) +
      Q.size (StepClass.HasProd.prod (rep.ty point₂) (rep.ty (machineStore qS))) (pk, saved) ≤ 32 * W by
        dsimp only [saved, Prod.fst, Prod.snd] at hp ⊢; dsimp only [W]; omega)
    change Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (initial qS))
      (g, g₂, X, pk, h, ()) + control.localCall (Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()))
        (Q.size (StepClass.HasProd.prod (rep.ty point₂) (rep.ty (machineStore qS))) (pk, saved)) ≤ _
    dsimp only [fee] at *
    omega
  have hd := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing
    (rep.ty (machineStore qS)) boundary.key (fun key => key = pk) (fun key => key = pk)
    (fun state => state = saved) W adapterTime
    (by intro key he; subst key; exact hk.trans (by dsimp [W]; omega))
    (by intro state he; subst state; exact hs.trans (by dsimp [W]; omega))
    (by intro key he; subst key; exact ⟨rfl, hb.1.trans (by dsimp [W]; omega), hb.2⟩)
  have hd' : Bounds control queryCost (.first (rep.ty (machineStore qS)) (.atomic (iface := iface) boundary.key))
      middle middle (adapterTime + 2 * fee) := by
    intro input hi z hz
    obtain ⟨hout, ht⟩ := hd input ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩ z hz
    exact ⟨Prod.ext hout.1 hout.2, ht⟩
  have hbound := Bounds.seq control queryCost _ _ (fun input => input = (g, g₂, X, pk, h, ()))
    middle middle (65 * fee) (adapterTime + 2 * fee) fee ha hd' (by
      intro input hi value hv
      subst input
      change value = (pk, saved) at hv
      subst value
      exact (routing.sequence _ _).trans (mono (by
        change Q.size (rep.env inputTypes) (g, g₂, X, pk, h, ()) +
          Q.size (StepClass.HasProd.prod (rep.ty point₂) (rep.ty (machineStore qS))) (pk, saved) ≤ 32 * W
        dsimp only [saved, Prod.fst, Prod.snd] at hp ⊢; dsimp only [W]; omega)))
  intro input hi z hz
  obtain ⟨hout, ht⟩ := hbound input hi z hz
  exact ⟨hout, by dsimp only [fee, W] at ht; omega⟩

end Signatures.Runtime.Coron.NativeSolver
