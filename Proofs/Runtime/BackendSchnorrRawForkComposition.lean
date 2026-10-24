import Proofs.Runtime.BackendSchnorrRawForkSize
import Proofs.Runtime.BackendWidthBudget

/-! Composition rules for the fork's proved frame footprints. These rules
charge every atomic invocation, sequence, branch and retained frame. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork.Frame

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {iface : Interface (C := C) unifSpec}
  {width cap : Nat} {overhead : Nat → Nat} (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

theorem widen {A B : Type} {a : C.Str A} {b : C.Str B}
    {code : Code Q unifSpec iface a b} {pre : A → Prop} {post : B → Prop} {t u : Nat}
    (h : Bounds control queryCost code pre post t) (ht : t ≤ u) :
    Bounds control queryCost code pre post u := by
  intro input hp z hz
  obtain ⟨ho, hc⟩ := h input hp z hz
  exact ⟨ho, hc.trans ht⟩

include mono routing

theorem atomic {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (localCode : Q.Realizer a b f) (pre : Frame (Q := Q) a width) (post : Frame (Q := Q) b width)
    (time : Nat) (hi : pre.factor ≤ cap) (ho : post.factor ≤ cap)
    (hp : ∀ input, pre.property input → post.property (f input))
    (ht : ∀ input, pre.property input → Q.cost localCode input ≤ time) :
    Bounds control queryCost (.atomic (iface := iface) localCode) pre.property post.property
      (time + overhead (256 * (cap * width))) := by
  apply Bounds.atomic
  intro input h
  have hout := hp input h
  have hin := (pre.size_le input h).trans (Nat.mul_le_mul_right width hi)
  have hsize := (post.size_le (f input) hout).trans (Nat.mul_le_mul_right width ho)
  have hc := (routing.localCall _ _).trans (mono (show Q.size a input + Q.size b (f input) ≤
    256 * (cap * width) by omega))
  exact ⟨hout, Nat.add_le_add (ht input h) hc⟩

theorem seq {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {initial : Code Q unifSpec iface a b} {following : Code Q unifSpec iface b d}
    (pre : Frame (Q := Q) a width) (middle : Frame (Q := Q) b width)
    (post : Frame (Q := Q) d width) {initialTime followingTime : Nat}
    (hiSize : pre.factor ≤ cap) (hmSize : middle.factor ≤ cap)
    (hi : Bounds control queryCost initial pre.property middle.property initialTime)
    (hf : Bounds control queryCost following middle.property post.property followingTime) :
    Bounds control queryCost (.seq initial following) pre.property post.property
      (initialTime + followingTime + overhead (256 * (cap * width))) := by
  apply Bounds.seq control queryCost initial following _ _ _ _ _ _ hi hf
  intro input hp value hv
  have hin := (pre.size_le input hp).trans (Nat.mul_le_mul_right width hiSize)
  have hout := (middle.size_le value hv).trans (Nat.mul_le_mul_right width hmSize)
  exact (routing.sequence _ _).trans (mono (by omega))

theorem first {A B S : Type} {a : C.Str A} {b : C.Str B} {s : C.Str S}
    {body : Code Q unifSpec iface a b} (pre : Frame (Q := Q) a width)
    (post : Frame (Q := Q) b width) (keep : Frame (Q := Q) s width) {time : Nat}
    (hs : keep.factor ≤ cap) (ho : post.factor ≤ cap)
    (hb : Bounds control queryCost body pre.property post.property time) :
    Bounds control queryCost (.first s body) (Both pre.property keep.property)
      (Both post.property keep.property) (time + overhead (256 * (cap * width))) := by
  apply Bounds.first control queryCost s body _ _ _ _ _ hb
  intro saved hs' out ho'
  have hsaved := (keep.size_le saved hs').trans (Nat.mul_le_mul_right width hs)
  have hout := (post.size_le out ho').trans (Nat.mul_le_mul_right width ho)
  exact (routing.retain _ _).trans (mono (by omega))

theorem branch {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {leftCode : Code Q unifSpec iface a d} {rightCode : Code Q unifSpec iface b d}
    (preLeft : Frame (Q := Q) a width) (preRight : Frame (Q := Q) b width)
    (preSum : Frame (Q := Q) (StepClass.HasSum.sum a b) width)
    (post : Frame (Q := Q) d width) {leftTime rightTime : Nat}
    (hpre : preSum.property = Sum.elim preLeft.property preRight.property)
    (hs : preSum.factor ≤ cap)
    (hl : Bounds control queryCost leftCode preLeft.property post.property leftTime)
    (hr : Bounds control queryCost rightCode preRight.property post.property rightTime) :
    Bounds control queryCost (.branch leftCode rightCode) preSum.property post.property
      (max leftTime rightTime + overhead (256 * (cap * width))) := by
  rw [hpre]
  apply Bounds.branch control queryCost leftCode rightCode _ _ _ _ _ _ hl hr
  intro input hp
  have hin := (preSum.size_le input (by simpa only [hpre] using hp)).trans
    (Nat.mul_le_mul_right width hs)
  exact (routing.branch _).trans (mono (by omega))

end Signatures.Runtime.Schnorr.RawTape.NativeFork.Frame
