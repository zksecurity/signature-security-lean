import Proofs.Runtime.BackendCallerRouting
import Proofs.Runtime.BackendBudget
import Proofs.Runtime.BackendDescriptionLaws
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! Independent pair sampling as actual common-backend code. Both component
samplers, value retention, pair construction, control, and stored descriptions
are charged. A pair sampler is a derived program, not an additional primitive.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.PairSampling

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd]
  {I A B : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  (data : DataRepresentation C) (construct : DataCode Q data)
  (a : C.Str A) (b : C.Str B)
  (left : Code Q spec iface data.unit a) (right : Code Q spec iface data.unit b)

def code : Code Q spec iface data.unit (StepClass.HasProd.prod a b) :=
  .seq left (.seq (.atomic (QP.pair (construct.unit a) (Q.identity a)))
    (.seq (.first a right) (.atomic (QP.pair (QP.snd b a) (QP.fst b a)))))

theorem denote (input : Unit) :
    (code data construct a b left right).denote input = (do
      let x ← left.denote input
      let y ← right.denote ()
      pure (x, y)) := by
  simp [code, Code.denote, bind_pure_comp]

theorem uniform [SampleableType A] [SampleableType B]
    {iface : Interface (C := C) unifSpec}
    (left : Code Q unifSpec iface data.unit a) (right : Code Q unifSpec iface data.unit b)
    (hl : ∀ input, left.denote input = ($ᵗ A : ProbComp A))
    (hr : ∀ input, right.denote input = ($ᵗ B : ProbComp B)) (input : Unit) :
    (code data construct a b left right).denote input = ($ᵗ (A × B) : ProbComp (A × B)) := by
  rw [denote, hl]
  change (do let x ← ($ᵗ A : ProbComp A); let y ← right.denote (); pure (x, y)) =
    ((Prod.mk <$> ($ᵗ A : ProbComp A)) <*> ($ᵗ B : ProbComp B))
  rw [hr]
  simp [seq_eq_bind_map, bind_map_left, bind_pure_comp]

variable [QS : Q.HasSum]

section Bounds

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws data construct overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes laws dataLaws mono routing

/-- The component budgets include their own full execution. The twelve added
charges cover two local adapters, retention, and all three sequences. -/
theorem bound (width leftTime rightTime : Nat)
    (hh : header ≤ width) (hu : Q.size data.unit () ≤ width)
    (hl : Bounds control queryCost left (fun _ => True) (fun x => Q.size a x ≤ width) leftTime)
    (hr : Bounds control queryCost right (fun _ => True) (fun y => Q.size b y ≤ width) rightTime) :
    Bounds control queryCost (code data construct a b left right) (fun _ => True)
      (fun p => Q.size a p.1 ≤ width ∧ Q.size b p.2 ≤ width)
      (leftTime + rightTime + 12 * overhead (8 * width)) := by
  let fee := overhead (8 * width)
  have packSize (x : A) (hx : Q.size a x ≤ width) :
      Q.size (StepClass.HasProd.prod data.unit a) ((), x) ≤ 3 * width := by
    have h := sizes.prod_le data.unit a ((), x)
    dsimp at h
    omega
  have baSize (y : B) (x : A) (hy : Q.size b y ≤ width) (hx : Q.size a x ≤ width) :
      Q.size (StepClass.HasProd.prod b a) (y, x) ≤ 3 * width := by
    have h := sizes.prod_le b a (y, x)
    dsimp at h
    omega
  have abSize (x : A) (y : B) (hx : Q.size a x ≤ width) (hy : Q.size b y ≤ width) :
      Q.size (StepClass.HasProd.prod a b) (x, y) ≤ 3 * width := by
    have h := sizes.prod_le a b (x, y)
    dsimp at h
    omega
  have pack : Bounds control queryCost
      (Code.atomic (iface := iface) (QP.pair (construct.unit a) (Q.identity a)))
      (fun x => Q.size a x ≤ width)
      (fun p => p.1 = () ∧ Q.size a p.2 ≤ width) (4 * fee) := by
    apply Bounds.atomic
    intro x hx
    refine ⟨⟨rfl, hx⟩, ?_⟩
    have hs := packSize x hx
    have hp := laws.pair (construct.unit a) (Q.identity a) x
    have hd := (dataLaws.unit a x).trans (mono (show Q.size a x + Q.size data.unit () ≤ 8 * width by omega))
    have hi := (laws.identity a x).trans (mono (show Q.size a x ≤ 8 * width by omega))
    have hc := (routing.localCall (Q.size a x) (Q.size (StepClass.HasProd.prod data.unit a) ((), x))).trans
      (mono (show Q.size a x + Q.size (StepClass.HasProd.prod data.unit a) ((), x) ≤ 8 * width by omega))
    have hf := mono (show Q.size a x + Q.size (StepClass.HasProd.prod data.unit a) ((), x) ≤ 8 * width by omega)
    dsimp only [fee, id_eq]
    dsimp at hp
    omega
  have draw : Bounds control queryCost (.first a right)
      (fun p => p.1 = () ∧ Q.size a p.2 ≤ width)
      (fun p => Q.size b p.1 ≤ width ∧ Q.size a p.2 ≤ width) (rightTime + fee) := by
    intro input hi z hz
    apply Bounds.first control queryCost a right (fun _ => True)
      (fun y => Q.size b y ≤ width) (fun x => Q.size a x ≤ width)
      rightTime fee hr ?_ input ⟨True.intro, hi.2⟩ z hz
    intro x hx y hy
    exact (routing.retain _ _).trans (mono (by omega))
  have swap : Bounds control queryCost
      (Code.atomic (iface := iface) (QP.pair (QP.snd b a) (QP.fst b a)))
      (fun p => Q.size b p.1 ≤ width ∧ Q.size a p.2 ≤ width)
      (fun p => Q.size a p.1 ≤ width ∧ Q.size b p.2 ≤ width) (4 * fee) := by
    apply Bounds.atomic
    intro p hp
    refine ⟨⟨hp.2, hp.1⟩, ?_⟩
    have hs := baSize p.1 p.2 hp.1 hp.2
    change Q.size (StepClass.HasProd.prod b a) p ≤ 3 * width at hs
    have ht := abSize p.2 p.1 hp.2 hp.1
    have hpair := laws.pair (QP.snd b a) (QP.fst b a) p
    have hf := (laws.fst b a p).trans (mono (show
      Q.size (StepClass.HasProd.prod b a) p + Q.size b p.1 ≤ 8 * width by omega))
    have hsnd := (laws.snd b a p).trans (mono (show
      Q.size (StepClass.HasProd.prod b a) p + Q.size a p.2 ≤ 8 * width by omega))
    have he := mono (show Q.size (StepClass.HasProd.prod b a) p +
      Q.size (StepClass.HasProd.prod a b) (p.2, p.1) ≤ 8 * width by omega)
    have hc := (routing.localCall _ _).trans he
    dsimp only [fee]
    omega
  have tail := Bounds.seq control queryCost (.first a right) _ _ _ _
    (rightTime + fee) (4 * fee) fee draw swap (by
      intro input hi output ho
      have hs := packSize input.2 hi.2
      have ht := baSize output.1 output.2 ho.1 ho.2
      change Q.size (StepClass.HasProd.prod b a) output ≤ 3 * width at ht
      apply (routing.sequence _ _).trans
      apply mono
      have he : input = ((), input.2) := by ext; simp
      rw [he]
      omega)
  have middle := Bounds.seq control queryCost _ _ _ _ _ (4 * fee)
    (rightTime + fee + 4 * fee + fee) fee pack tail (by
      intro input hi output ho
      have hs := packSize output.2 ho.2
      apply (routing.sequence _ _).trans
      apply mono
      simpa only [ho.1] using (show Q.size a input +
        Q.size (StepClass.HasProd.prod data.unit a) ((), output.2) ≤ 8 * width by omega))
  have complete := Bounds.seq control queryCost left _ _ _ _ leftTime
    (4 * fee + (rightTime + fee + 4 * fee + fee) + fee) fee hl middle (by
      intro input _ output ho
      cases input
      change control.sequence (Q.size data.unit ()) (Q.size a output) ≤ fee
      exact (routing.sequence _ _).trans (mono (by omega)))
  convert complete using 1 <;> simp only [code, fee]; omega

end Bounds

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes data construct allowance) :
    (code data construct a b left right).descriptionSize sizes ≤
      left.descriptionSize sizes + right.descriptionSize sizes + 6 * allowance + 6 := by
  have hp := laws.pair_bound (dataLaws.unit a) (laws.identity a)
  have hs := laws.pair_bound (laws.snd b a) (laws.fst b a)
  dsimp only [code, Code.descriptionSize]
  omega

end Signatures.Runtime.BackendProgram.PairSampling
