import Signatures.Runtime.BackendSchnorrAGMExtractionDescription
import Signatures.Runtime.BackendDispatchBudget

/-! Executable conversion of the general caller's final output. The caller's
representation is decoded by an actual local backend realizer; dropping the
public configuration, retaining the whole state and conversion are all charged.
The encoding function alone is never used as a free executable operation. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Solver

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C} [Q.HasCategory] [QP : Q.HasProd]
  {F G₁ G₂ K M Input : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input (SourceForgery F G₁ M))
  (convert : Q.Realizer bd.out (rep.ty forgeryTy) encodeForgery)

def outputArgs : Q.Realizer (StepClass.HasProd.prod bd.out (rep.ty storeTy))
    (StepClass.HasProd.prod bd.out (rep.ty stateTy)) (fun p => (p.1, p.2.2)) :=
  QP.pair (QP.fst bd.out (rep.ty storeTy))
    (Q.compose (QP.snd bd.out (rep.ty storeTy)) (QP.snd (rep.ty configTy) (rep.ty stateTy)))

def adaptOutput {iface : BackendProgram.Interface (C := C) unifSpec} :
    Code Q unifSpec iface (StepClass.HasProd.prod bd.out (rep.ty storeTy)) (rep.ty Extraction.inputTy) :=
  .seq (.atomic (outputArgs (Q := Q) rep bd)) (.first (rep.ty stateTy) (.atomic convert))

theorem adaptOutput_denote {iface : BackendProgram.Interface (C := C) unifSpec}
    (out : SourceForgery F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (adaptOutput (iface := iface) rep bd convert).denote (out, saved) = pure (encodeForgery out, saved.2) := by
  simp only [adaptOutput, Code.denote, map_pure, pure_bind]

variable [QS : Q.HasSum]

theorem outputArgs_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance) :
    sizes.localSize (outputArgs (Q := Q) rep bd) ≤ 5 * allowance := by
  exact (laws.pair_bound (laws.fst bd.out (rep.ty storeTy))
    (laws.compose_bound (laws.snd bd.out (rep.ty storeTy)) (laws.snd (rep.ty configTy) (rep.ty stateTy)))).trans (by omega)

theorem adaptOutput_description {iface : BackendProgram.Interface (C := C) unifSpec}
    (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance) :
    (adaptOutput (iface := iface) rep bd convert).descriptionSize sizes ≤
      sizes.localSize convert + 5 * allowance + 4 := by
  have h := outputArgs_description rep bd sizes allowance laws
  dsimp only [adaptOutput, Code.descriptionSize]
  omega

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)

include sizes laws mono

theorem outputArgs_cost (input : SourceForgery F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M))
    (width : Nat) (hh : header ≤ width)
    (ho : Q.size bd.out input.1 ≤ width) (hs : Q.size (rep.ty storeTy) input.2 ≤ width) :
    Q.cost (outputArgs (Q := Q) rep bd) input ≤ 5 * overhead (32 * width) := by
  have h := (LocalBound.pair laws (LocalBound.fst laws bd.out (rep.ty storeTy))
    (LocalBound.compose laws (LocalBound.snd laws bd.out (rep.ty storeTy))
      (LocalBound.snd laws (rep.ty configTy) (rep.ty stateTy)))).cost_le input
  have hstate := (sizes.snd_le (rep.ty configTy) (rep.ty stateTy) input.2).trans hs
  have hin := sizes.prod_le bd.out (rep.ty storeTy) input
  have hout := sizes.prod_le bd.out (rep.ty stateTy) (input.1, input.2.2)
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  change Q.cost (outputArgs (Q := Q) rep bd) input ≤ _ at h
  refine h.trans ?_
  dsimp only [LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.compose, Function.comp_def]
  dsimp only at hin hout
  grind only

variable {iface : BackendProgram.Interface (C := C) unifSpec}
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

/-- The only conversion-cost premise concerns the actual local representation
adapter. The full wrapper and its retained-state/control overhead are derived. -/
theorem adaptOutput_bound (width adapterTime : Nat) (hh : header ≤ width)
    (keep : EncodedState F G₁ M → Prop)
    (hconvert : ∀ out, Q.size bd.out out ≤ width →
      Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ width ∧ Q.cost convert out ≤ adapterTime) :
    Bounds control queryCost (adaptOutput (iface := iface) rep bd convert)
      (fun p => Q.size bd.out p.1 ≤ width ∧ Q.size (rep.ty storeTy) p.2 ≤ width ∧ keep p.2.2)
      (fun p => Q.size (rep.ty forgeryTy) p.1 ≤ width ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2)
      (adapterTime + 9 * overhead (32 * width)) := by
  let fee := overhead (32 * width)
  let pre := fun p : SourceForgery F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M) =>
    Q.size bd.out p.1 ≤ width ∧ Q.size (rep.ty storeTy) p.2 ≤ width ∧ keep p.2.2
  let middle := fun p : SourceForgery F G₁ M × EncodedState F G₁ M =>
    Q.size bd.out p.1 ≤ width ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2
  let post := fun p : Extraction.inputTy.Value (cryptoBase F G₁ G₂ K M) =>
    Q.size (rep.ty forgeryTy) p.1 ≤ width ∧ Q.size (rep.ty stateTy) p.2 ≤ width ∧ keep p.2
  have hpre (input) (hi : pre input) : Q.size (StepClass.HasProd.prod bd.out (rep.ty storeTy)) input ≤ 3 * width := by
    have ho := hi.1
    have hs := hi.2.1
    exact (sizes.prod_le bd.out (rep.ty storeTy) input).trans (by omega)
  have hmid (input) (hi : middle input) : Q.size (StepClass.HasProd.prod bd.out (rep.ty stateTy)) input ≤ 3 * width := by
    have ho := hi.1
    have hs := hi.2.1
    exact (sizes.prod_le bd.out (rep.ty stateTy) input).trans (by omega)
  have hstart : Bounds control queryCost (.atomic (iface := iface) (outputArgs (Q := Q) rep bd)) pre middle (6 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho : middle (input.1, input.2.2) :=
      ⟨hi.1, (sizes.snd_le (rep.ty configTy) (rep.ty stateTy) input.2).trans hi.2.1, hi.2.2⟩
    have hin := hpre input hi
    have hout := hmid (input.1, input.2.2) ho
    have ht := outputArgs_cost rep bd sizes laws mono input width hh hi.1 hi.2.1
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (StepClass.HasProd.prod bd.out (rep.ty storeTy)) input +
        Q.size (StepClass.HasProd.prod bd.out (rep.ty stateTy)) (input.1, input.2.2) ≤ 32 * width by omega))
    refine ⟨ho, ?_⟩
    dsimp only [fee]
    omega
  have hconvert := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty stateTy) convert
    (fun out => Q.size bd.out out ≤ width) (fun out => Q.size (rep.ty forgeryTy) out ≤ width)
    (fun saved => Q.size (rep.ty stateTy) saved ≤ width ∧ keep saved) width adapterTime
    (fun _ h => h) (fun _ h => h.1) (by intro out ho; exact ⟨(hconvert out ho).1, hconvert out ho⟩)
  have hall := Bounds.seq control queryCost _ _ pre middle post (6 * fee) (adapterTime + 2 * fee) fee hstart hconvert (by
    intro input hi output ho
    have hin := hpre input hi
    have hout := hmid output ho
    exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi z hrun
  obtain ⟨ho, ht⟩ := hall input hi z hrun
  exact ⟨ho, by dsimp only [fee] at *; omega⟩

end Signatures.Runtime.SchnorrAGM.Native.Solver
