import Signatures.Runtime.GeneralCallerGrowth
import Signatures.Runtime.CoronMachineReduction

/-! The lazy BLS co-CDH simulator with a general, backend-realized caller.

The request interface bounds randomness arity, but imposes no arithmetic-language
restriction on local computation. Message/group encodings are the caller's
backend representations. These are mixed-model accounting theorems; the common
backend implementation contracts and solver hardness endpoint are separate.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron

abbrev GeneralRequest (M : Type) (randomBound : Nat) :=
  (Fin (randomBound + 1) ⊕ M) ⊕ M

def generalSpec (M G₁ : Type) (randomBound : Nat) : OracleSpec (GeneralRequest M randomBound)
  | .inl (.inl n) => Fin (n.val + 1)
  | .inl (.inr _) => G₁
  | .inr _ => G₁

def generalKind {M : Type} {randomBound : Nat} : GeneralRequest M randomBound → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def generalReplies (M G₁ : Type) [Zero G₁] (randomBound : Nat) :
    GeneralCaller.ReplyContract (generalSpec M G₁ randomBound) where
  allows _ _ := True
  responds i := by
    rcases i with (n | m) | m
    · exact ⟨(0 : Fin (n.val + 1)), trivial⟩
    · exact ⟨(0 : G₁), trivial⟩
    · exact ⟨(0 : G₁), trivial⟩

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

/-- Each request runs the existing arithmetic-machine handler, including its
procedure-call cost. The caller's initialization/head/update costs remain separate. -/
noncomputable def generalHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) : GeneralCaller.Handler (spec := generalSpec M G₁ randomBound)
      (StateT ((machineStore qS).Value (cryptoBase F G₁ G₂ M M)) ProbComp)
  | .inl (.inl n) => machineHandler cost sampling qS randomBound (.random n) ()
  | .inl (.inr m) => machineHandler cost sampling qS randomBound .hash m
  | .inr m => machineHandler cost sampling qS randomBound .sign m

theorem generalHandler_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound : Nat) (i : GeneralRequest M randomBound)
    (state : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (z : Run ((generalSpec M G₁ randomBound).Range i) ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support ((generalHandler cost sampling qS randomBound i).run state)) :
    (machineCaches z.2).size ≤ (machineCaches state).size + 1 ∧
      z.1.steps ≤ machinePrices cost sampling qS randomBound (generalKind i) +
        2 * (cost.messageEq + 19) * (machineCaches state).size := by
  rcases i with (n | m) | m
  · exact machineHandler_bound cost sampling qS randomBound (.random n) () state z hz
  · exact machineHandler_bound cost sampling qS randomBound .hash m state z hz
  · exact machineHandler_bound cost sampling qS randomBound .sign m state z hz

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} {randomBound : Nat}
  {bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁)}

/-- The general caller plus the existing lazy simulator has quadratic cache
overhead in its query count. No completed-simulator bound is a premise. -/
theorem generalSimulation_bound
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel localTime : Nat) (queries : Fin 3 → Nat)
    (hcaller : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind
      fuel pk localTime queries)
    (z : Run (Option (M × G₁)) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support ((GeneralCaller.run R (generalHandler cost sampling qS randomBound)
      fuel pk).run (machineState g X h .empty))) :
    (machineCaches z.2).size ≤ ∑ k, queries k ∧
      z.1.steps ≤ localTime + (∑ k, queries k * machinePrices cost sampling qS randomBound k) +
        2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 := by
  have hb := GeneralCaller.Budget.linear_state_bound R (generalReplies M G₁ randomBound)
    generalKind fuel pk localTime queries hcaller (generalHandler cost sampling qS randomBound)
    (machinePrices cost sampling qS randomBound) (2 * (cost.messageEq + 19))
    (fun _ => True) (fun s => (machineCaches s).size) (by
      intro i state _ out hout
      exact ⟨trivial, trivial, generalHandler_bound cost sampling qS randomBound i state out hout⟩)
    (machineState g X h .empty) trivial rfl z hz
  exact hb.2

/-- The general caller followed by the existing final-hash/extraction routine.
The sixteen fixed adapter charges cover constructing the empty wrapper state,
dispatching on termination, the finish call, and return packing in this mixed
accounting model. Their common-backend realization remains a separate obligation.
Fuel exhaustion is retained as `none`, never replaced by a fabricated forgery. -/
noncomputable def generalReduction
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel : Nat) : ProbComp (Run (Option G₁)) := do
  let p ← (GeneralCaller.run R (generalHandler cost sampling qS randomBound) fuel pk).run
    (machineState g X h .empty)
  match p.1.value with
  | none => pure ⟨none, p.1.steps + 16⟩
  | some out =>
      let r ← ((machineFinish qS).run (arithmetic F G₁ G₂ M M cost)
        (Machine.effects sampling (machineStore qS)) (out, ())).run p.2
      pure ⟨some r.1.value, p.1.steps + r.1.steps + 16⟩

def generalReductionBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (qS randomBound localTime : Nat) (queries : Fin 3 → Nat) : Nat :=
  localTime + (∑ k, queries k * machinePrices cost sampling qS randomBound k) +
    2 * (cost.messageEq + 19) * (∑ k, queries k) ^ 2 +
    finishBound cost (machineSampling sampling qS) (∑ k, queries k) + cost.natOp + 96

/-- Includes the extra final hash even when the attacker never queried its
eventual target. No enumeration of the message universe occurs in the runner. -/
theorem generalReduction_bound
    (R : GeneralCaller.Caller (Q := Q) (bd := bd))
    (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (g X h : G₁) (pk : G₂) (qS fuel localTime : Nat) (queries : Fin 3 → Nat)
    (hcaller : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind
      fuel pk localTime queries)
    (z : Run (Option G₁))
    (hz : z ∈ support (generalReduction (F := F) R cost sampling g X h pk qS fuel)) :
    z.steps ≤ generalReductionBound cost sampling qS randomBound localTime queries := by
  simp only [generalReduction, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  have hs := generalSimulation_bound R cost sampling g X h pk qS fuel localTime queries
    hcaller p hp
  cases hv : p.1.value with
  | none =>
      simp only [hv, support_pure, Set.mem_singleton_iff] at hz
      subst z
      dsimp [generalReductionBound]
      omega
  | some out =>
      simp only [hv, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      rcases p with ⟨result, ⟨⟨g', X', h'⟩, scalars, coins, signed⟩⟩
      have hf := machineFinish_bound cost sampling g' X' h' qS out
        ⟨scalars, coins, signed⟩ r hr
      have hm := Nat.mul_le_mul_left (cost.messageEq + 19) (Nat.mul_le_mul_left 3 hs.1)
      dsimp [machineCaches, generalReductionBound, finishBound] at hs hf hm ⊢
      nlinarith [hs.2]

end Signatures.Runtime.Coron
