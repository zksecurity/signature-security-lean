import Proofs.Runtime.BackendBudget
import Proofs.Runtime.BackendCallerRouting

/-! Native composition with explicit bounds on the encoded values crossing each
boundary. These rules charge local invocation, sequencing, and retained storage;
the component execution bounds remain separate proved premises. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {overhead : Nat → Nat} (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include mono routing

theorem atomic_bound_of_width {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (pre : A → Prop) (post : B → Prop) (width time : Nat)
    (hi : ∀ input, pre input → Q.size a input ≤ width)
    (hl : ∀ input, pre input → post (f input) ∧ Q.size b (f input) ≤ width ∧ Q.cost code input ≤ time) :
    Bounds control queryCost (.atomic (iface := iface) code) pre post
      (time + overhead (32 * width)) := by
  apply Bounds.atomic
  intro input hp
  obtain ⟨hout, hw, ht⟩ := hl input hp
  have hc := (routing.localCall (Q.size a input) (Q.size b (f input))).trans
    (mono (show Q.size a input + Q.size b (f input) ≤ 32 * width by have := hi input hp; omega))
  exact ⟨hout, Nat.add_le_add ht hc⟩

theorem seq_bound_of_width {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (initial : Code Q spec iface a b) (following : Code Q spec iface b d)
    (pre : A → Prop) (middle : B → Prop) (post : D → Prop) (width initialTime followingTime : Nat)
    (hiSize : ∀ input, pre input → Q.size a input ≤ width)
    (hmSize : ∀ value, middle value → Q.size b value ≤ width)
    (hi : Bounds control queryCost initial pre middle initialTime)
    (hf : Bounds control queryCost following middle post followingTime) :
    Bounds control queryCost (.seq initial following) pre post
      (initialTime + followingTime + overhead (32 * width)) := by
  apply Bounds.seq control queryCost initial following pre middle post _ _ _ hi hf
  intro input hp value hv
  exact (routing.sequence _ _).trans (mono (by have := hiSize input hp; have := hmSize value hv; omega))

theorem first_bound_of_width {A B S : Type} {a : C.Str A} {b : C.Str B}
    (store : C.Str S) (body : Code Q spec iface a b)
    (pre : A → Prop) (post : B → Prop) (keep : S → Prop) (width time : Nat)
    (hs : ∀ saved, keep saved → Q.size store saved ≤ width)
    (ho : ∀ out, post out → Q.size b out ≤ width)
    (hb : Bounds control queryCost body pre post time) :
    Bounds control queryCost (.first store body) (fun p => pre p.1 ∧ keep p.2)
      (fun p => post p.1 ∧ keep p.2) (time + overhead (32 * width)) := by
  apply Bounds.first control queryCost store body pre post keep time _ hb
  intro saved hs' out ho'
  exact (routing.retain _ _).trans (mono (by have := hs saved hs'; have := ho out ho'; omega))

end Signatures.Runtime.BackendProgram
