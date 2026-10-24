import Proofs.Runtime.BackendWeightedSolverLocalCost
import Proofs.Runtime.BackendWeightedSolverPorts

/-! Complete native challenge-setup bounds. Both branches construct empty
private state; the bad branch also samples its signing key and multiplies the
G2 generator. Retaining/copying the challenge and boundary key conversion are
charged, with no setup-cost premise. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeSolver

open BackendProgram NativeHandler Reply

def setupWidth (index : Index) (inputWidth width routeWidth cap : Nat) : Nat :=
  inputWidth + routeWidth + handlerStoreWidth index width cap

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor G₂
    ((AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M)))
  (boundary : DataPorts (Q := Q) rep index bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws primitiveBound mono routing

omit [SampleableType F] in
theorem setupGood_bound (inputWidth width outputWidth routeWidth cap adapterTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hk : ∀ pk : G₂, Q.size (rep.ty point₂) pk ≤ width)
    (caps : PortCaps rep index bd boundary width outputWidth routeWidth adapterTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (setupGood (iface := iface) rep index bd boundary data cost primitive)
      (fun input => input = (g, X, g₂, pk, ()))
      (fun out => out = (pk, (g, X), [], ([], [])))
      (adapterTime + 70 * overhead (128 * setupWidth index inputWidth width routeWidth cap)) := by
  let W := setupWidth index inputWidth width routeWidth cap
  have hw : width ≤ W := by
    have h := handlerStoreWidth_ge index width cap
    dsimp only [W, setupWidth]
    omega
  have hin : inputWidth ≤ W := by dsimp [W, setupWidth]; omega
  have hr : routeWidth ≤ W := by dsimp [W, setupWidth]; omega
  have hs := goodReserved_size rep index sizes lists width cap 0 hh hf hg ((g, X), [], ([], []))
    (initial_reserved rep index scalar LazyAGM.goodConfigTy width cap 0 (Nat.zero_le cap) (g, X))
  have hsW : Q.size (rep.ty (Reply.storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) ((g, X), [], ([], [])) ≤ W :=
    hs.trans (by dsimp [W, setupWidth]; omega)
  have hkey := caps.key pk (hk pk)
  have ht := initialGood_cost rep index data cost primitive sizes lists laws dataLaws primitiveBound mono
    W (hh.trans hw) (hu.trans hw) (g, X, g₂, pk, ()) (hi.trans hin)
  intro input he z hz
  subst input
  simp only [setupGood, Code.run, sequenceRun, retainRun, map_pure, pure_bind,
    support_pure, Set.mem_singleton_iff] at hz
  subst z
  refine ⟨rfl, ?_⟩
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hretain := routing.retain
  have hfee : ∀ n ≤ 128 * W, overhead n ≤ overhead (128 * W) := fun _ hn => mono hn
  have hpk := hk pk
  dsimp only [initialGood, LazyAGM.ReplySyntax.v0, LazyAGM.ReplySyntax.v1, LazyAGM.ReplySyntax.v3, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, inputTypes, id] at *
  grind only

theorem setupBad_bound (inputWidth width outputWidth routeWidth cap adapterTime scalarTime scaleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hk : ∀ pk : G₂, Q.size (rep.ty point₂) pk ≤ width)
    (caps : PortCaps rep index bd boundary width outputWidth routeWidth adapterTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hscale : ∀ f : F, ∀ g : G₂, (primitiveBound CryptoOp.scale₂).time (f, g) ≤ scaleTime)
    (g X : G₁) (g₂ pk : G₂)
    (hi : Q.size (rep.env inputTypes) (g, X, g₂, pk, ()) ≤ inputWidth) :
    Bounds control queryCost (setupBad rep index bd boundary data cost primitive sampling)
      (fun input => input = (g, X, g₂, pk, ()))
      (fun out => ∃ kappa : F, out = (kappa • g₂, (kappa, g, X), [], ([], [])))
      (scalarTime + scaleTime + adapterTime + 112 * overhead (512 * setupWidth index inputWidth width routeWidth cap)) := by
  let W := setupWidth index inputWidth width routeWidth cap
  have hw : width ≤ W := by
    have h := handlerStoreWidth_ge index width cap
    dsimp only [W, setupWidth]
    omega
  have hin : inputWidth ≤ W := by dsimp [W, setupWidth]; omega
  have hr : routeWidth ≤ W := by dsimp [W, setupWidth]; omega
  intro input he z hz
  subst input
  simp only [setupBad, Code.run, sequenceRun, retainRun, map_pure, pure_bind,
    bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨middle, hm, rfl⟩ := hz
  obtain ⟨sample, hsampled, rfl⟩ := hm
  have htime := hsample sample hsampled
  have hkey := caps.key (sample.value • g₂) (hk _)
  have hs := badReserved_size rep index sizes lists width cap 0 hh hf hg ((sample.value, g, X), [], ([], []))
    (initial_reserved rep index (.pair scalar scalar) LazyAGM.badConfigTy width cap 0 (Nat.zero_le cap) (sample.value, g, X))
  have hsW : Q.size (rep.ty (Reply.storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) ((sample.value, g, X), [], ([], [])) ≤ W :=
    hs.trans (by dsimp [W, setupWidth]; omega)
  have henv : Q.size (rep.env (scalar :: inputTypes)) (sample.value, g, X, g₂, pk, ()) ≤ 3 * W := by
    have hp := sizes.prod_le (rep.ty scalar) (rep.env inputTypes) (sample.value, g, X, g₂, pk, ())
    have hscalar := hf sample.value
    change Q.size (StepClass.HasProd.prod (rep.ty scalar) (rep.env inputTypes))
      (sample.value, g, X, g₂, pk, ()) ≤ 3 * W
    dsimp only at hp
    omega
  have ht := initialBad_cost rep index data cost primitive sizes lists laws dataLaws primitiveBound mono
    (3 * W) scaleTime (by omega) (by omega) (fun pk => (hk pk).trans (by omega)) hscale
    (sample.value, g, X, g₂, pk, ()) henv
  refine ⟨⟨sample.value, rfl⟩, ?_⟩
  have hid := laws.identity (rep.env inputTypes) (g, X, g₂, pk, ())
  have hunit := dataLaws.unit (rep.env inputTypes) (g, X, g₂, pk, ())
  have hpair := laws.pair (data.unit (rep.env inputTypes)) (Q.identity (rep.env inputTypes)) (g, X, g₂, pk, ())
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hretain := routing.retain
  have hfee : ∀ n ≤ 512 * W, overhead n ≤ overhead (512 * W) := fun _ hn => mono hn
  have hscalar := hf sample.value
  have hpk := hk (sample.value • g₂)
  dsimp only [initialBad, LazyAGM.ReplySyntax.v0, LazyAGM.ReplySyntax.v1, LazyAGM.ReplySyntax.v2, LazyAGM.ReplySyntax.v3,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env, inputTypes, id, arithmetic] at *
  grind only

end Signatures.Runtime.WeightedAGM.NativeSolver
