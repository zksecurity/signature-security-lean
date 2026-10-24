import Proofs.Runtime.BackendSchnorrAGMSolverLocalCost

/-! Complete initialization budget and caller capacity invariant. The initial
basis contains two cells, the other histories are empty, and all future queries
have reserved capacity. Every construction and actual input conversion is paid. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

def setupWidth (inputWidth width routeWidth : Nat) : Nat := inputWidth + routeWidth + 64 * width

def setupTime (overhead : Nat → Nat) (inputWidth width routeWidth fieldTime adapterTime : Nat) : Nat :=
  4 * fieldTime + adapterTime + 1028 * overhead (1024 * setupWidth inputWidth width routeWidth)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor (SourceInput G₁) (SourceForgery F G₁ M))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws primitiveBound mono routing

theorem setup_bound (inputWidth width routeWidth cap basisCap signedCap fuel fieldTime adapterTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hc : fuel ≤ cap) (hn : fuel + 2 ≤ basisCap) (hs : fuel ≤ signedCap)
    (hzero : (primitiveBound .zero).time () ≤ fieldTime) (hone : (primitiveBound .one).time () ≤ fieldTime)
    (hinput : ∀ config, Q.size (rep.ty configTy) config ≤ 3 * width →
      Q.size bd.input (Schnorr.AGM.initial config.1 config.2) ≤ routeWidth ∧ Q.cost boundary.input config ≤ adapterTime) :
    Bounds control queryCost (setup (iface := iface) rep bd boundary data cost primitive)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth)
      (fun out => Handler.ReservedState (Q := Q) rep width cap basisCap signedCap fuel out.2 ∧
        Q.size bd.input out.1 ≤ routeWidth)
      (setupTime overhead inputWidth width routeWidth fieldTime adapterTime) := by
  let W := setupWidth inputWidth width routeWidth
  have hw : width ≤ W := by dsimp [W, setupWidth]; omega
  have hiw : inputWidth ≤ W := by dsimp [W, setupWidth]; omega
  have hrw : routeWidth ≤ W := by dsimp [W, setupWidth]; omega
  intro input hi z hz
  rcases input with ⟨g, pk, u⟩
  cases u
  have hreserved := initial_reserved rep width cap basisCap signedCap fuel hc hn hs g pk (hg g) (hg pk)
  have hcfg : Q.size (rep.ty configTy) (g, pk) ≤ 3 * width :=
    HandlerComponents.config_size rep sizes width hh (g, pk) ⟨hg g, hg pk⟩
  have hport := hinput (g, pk) hcfg
  have hstore := HandlerComponents.store_size rep sizes lists width 0 2 0 hh hb hf
    ((g, pk), encodeState ({} : State F G₁ M))
    (initial_reserved rep width 0 2 0 0 (by omega) (by omega) (by omega) g pk (hg g) (hg pk)).store
  have hstoreW : Q.size (rep.ty storeTy) ((g, pk), encodeState ({} : State F G₁ M)) ≤ W :=
    hstore.trans (by dsimp only [W, setupWidth]; omega)
  have ht := initial_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono W fieldTime
    (hh.trans hw) (hu.trans hw) ((hb false).trans hw) ((hf 0).trans hw) ((hf 1).trans hw) hzero hone
    (g, pk, ()) (hi.trans hiw)
  simp only [setup, Code.run, sequenceRun, retainRun, map_pure, pure_bind,
    support_pure, Set.mem_singleton_iff] at hz
  subst z
  refine ⟨⟨hreserved, hport.1⟩, ?_⟩
  let saved := ((g, pk), encodeState ({} : State F G₁ M))
  let middle := ((g, pk), saved)
  change Q.size (rep.ty storeTy) saved ≤ W at hstoreW
  have hin : Q.size (rep.env inputTypes) (g, pk, ()) ≤ W := hi.trans hiw
  change Q.size bd.input (Schnorr.AGM.initial g pk) ≤ routeWidth ∧ Q.cost boundary.input (g, pk) ≤ adapterTime at hport
  have hmid : Q.size (rep.ty (.pair configTy storeTy)) middle ≤ 5 * W := by
    have hp := sizes.prod_le (rep.ty configTy) (rep.ty storeTy) middle
    change _ ≤ Q.size (rep.ty configTy) (g, pk) + Q.size (rep.ty storeTy) saved + header at hp
    exact hp.trans (by omega)
  have hportWidth := hport.1
  have hportTime := hport.2
  have hcallInitial := (routing.localCall _ _).trans (mono (show
    Q.size (rep.env inputTypes) (g, pk, ()) + Q.size (rep.ty (.pair configTy storeTy)) middle ≤ 1024 * W by omega))
  have hcallPort := (routing.localCall _ _).trans (mono (show
    Q.size (rep.ty configTy) (g, pk) + Q.size bd.input (Schnorr.AGM.initial g pk) ≤ 1024 * W by omega))
  have hretain := (routing.retain _ _).trans (mono (show
    Q.size (rep.ty storeTy) saved + Q.size bd.input (Schnorr.AGM.initial g pk) ≤ 1024 * W by omega))
  have hsequence := (routing.sequence _ _).trans (mono (show
    Q.size (rep.env inputTypes) (g, pk, ()) + Q.size (rep.ty (.pair configTy storeTy)) middle ≤ 1024 * W by omega))
  change (Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive initialExpression) (g, pk, ()) +
    control.localCall (Q.size (rep.env inputTypes) (g, pk, ())) (Q.size (rep.ty (.pair configTy storeTy)) middle)) +
    (Q.cost boundary.input (g, pk) + control.localCall (Q.size (rep.ty configTy) (g, pk))
      (Q.size bd.input (Schnorr.AGM.initial g pk)) + control.retain (Q.size (rep.ty storeTy) saved)
        (Q.size bd.input (Schnorr.AGM.initial g pk))) +
    control.sequence (Q.size (rep.env inputTypes) (g, pk, ())) (Q.size (rep.ty (.pair configTy storeTy)) middle) ≤
      4 * fieldTime + adapterTime + 1028 * overhead (1024 * W)
  omega

end Signatures.Runtime.SchnorrAGM.Native.Solver
