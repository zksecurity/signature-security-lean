import Proofs.Runtime.BackendCallerRouting
import Proofs.Runtime.BackendBudget

/-! A single runtime-selected uniform query, with implemented request/reply
conversions. The program and its stored description do not enumerate arities. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.UniformSampling

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  (data : DataRepresentation C) {iface : Interface (C := C) unifSpec}

structure Ports where
  request : Q.Realizer data.nat iface.position id
  response : Q.Realizer iface.response data.nat (fun p => p.2.val)

variable (ports : Ports (Q := Q) data (iface := iface))

def code : Code Q unifSpec iface data.nat data.nat :=
  .seq (.atomic ports.request) (.seq .query (.atomic ports.response))

theorem denote (n : Nat) :
    (code data ports).denote n = Fin.val <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [code, Code.denote, id_eq, pure_bind, bind_pure_comp, Functor.map_map]

theorem description (sizes : DescriptionSize Q) :
    (code data ports).descriptionSize sizes =
      sizes.localSize ports.request + sizes.localSize ports.response + 5 := by
  dsimp only [code, Code.descriptionSize]
  omega

variable {overhead : Nat → Nat} (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include mono routing

theorem bound (width arityCap requestTime responseTime drawTime : Nat)
    (hn : ∀ n ≤ arityCap, Q.size data.nat n ≤ width)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hrequest : ∀ n ≤ arityCap, Q.cost ports.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost ports.response ⟨n, r⟩ ≤ responseTime)
    (hdraw : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ drawTime) :
    Bounds control queryCost (code data ports) (fun n => n ≤ arityCap)
      (fun r => r ≤ arityCap ∧ Q.size data.nat r ≤ width)
      (requestTime + responseTime + drawTime + 4 * overhead (8 * width)) := by
  let fee := overhead (8 * width)
  let pre := fun n => n ≤ arityCap
  let drawn := fun p : (Σ n, Fin (n + 1)) => p.1 ≤ arityCap
  let post := fun r => r ≤ arityCap ∧ Q.size data.nat r ≤ width
  have hreq : Bounds control queryCost (.atomic (iface := iface) ports.request) pre pre (requestTime + fee) := by
    apply Bounds.atomic
    intro n h
    have h₁ := hn n h
    have h₂ := hp n h
    have hc := (routing.localCall _ _).trans (mono (show Q.size data.nat n + Q.size iface.position n ≤ 8 * width by omega))
    exact ⟨h, Nat.add_le_add (hrequest n h) hc⟩
  have hquery : Bounds control queryCost (.query (Q := Q) (iface := iface)) pre drawn drawTime := by
    apply Bounds.query
    intro n h r
    exact ⟨h, hdraw n h r⟩
  have hresp : Bounds control queryCost (.atomic (iface := iface) ports.response) drawn post (responseTime + fee) := by
    apply Bounds.atomic
    rintro ⟨n, r⟩ h
    have hvalue : r.val ≤ arityCap := by have := r.isLt; dsimp only [drawn] at h; omega
    have h₁ := hr n h r
    have h₂ := hn r.val hvalue
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size iface.response ⟨n, r⟩ + Q.size data.nat r.val ≤ 8 * width by omega))
    exact ⟨⟨hvalue, h₂⟩, Nat.add_le_add (hresponse n h r) hc⟩
  have htail := Bounds.seq control queryCost _ _ pre drawn post drawTime (responseTime + fee) fee hquery hresp (by
    rintro n hn' ⟨m, r⟩ hp'
    have h₁ := hp n hn'
    have h₂ := hr m hp' r
    exact (routing.sequence _ _).trans (mono (by omega)))
  have hall := Bounds.seq control queryCost _ _ pre pre post (requestTime + fee)
    (drawTime + (responseTime + fee) + fee) fee hreq htail (by
      intro n hn' m hm
      have h₁ := hn n hn'
      have h₂ := hp m hm
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro n hn' out hout
  obtain ⟨ho, ht⟩ := hall n hn' out hout
  exact ⟨ho, ht.trans (by dsimp only [fee]; omega)⟩

end Signatures.Runtime.BackendProgram.UniformSampling
