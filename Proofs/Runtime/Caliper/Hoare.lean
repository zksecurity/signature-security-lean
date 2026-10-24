import Proofs.Runtime.Caliper.Routine
import Caliper.Triple

/-! Compositional verification of hybrid programs, using Caliper's own rules.
Lowering preserves the complete state and execution profile by construction.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {CallType : Type} {cost : CostModel} {tape : RandomTape w}
  {library : Library w CallType}

abbrev Triple (cost : CostModel) (tape : RandomTape w) (library : Library w CallType)
    (pre : State w → Prop) (program : Program w CallType) (post : State w → Prop)
    (time : Nat) (net peak : Int) :=
  Caliper.Triple cost tape pre (program.lower library) post time net peak

theorem Triple.seq {P R Q : State w → Prop} {first second : Program w CallType}
    {T₁ T₂ : Nat} {D₁ D₂ M₁ M₂ : Int}
    (hf : Triple cost tape library P first R T₁ D₁ M₁)
    (hs : Triple cost tape library R second Q T₂ D₂ M₂) :
    Triple cost tape library P (.seq first second) Q
      (T₁ + T₂) (D₁ + D₂) (max M₁ (D₁ + M₂)) :=
  Caliper.Triple.seq hf hs

theorem Triple.branch {P Q : State w → Prop} {yes no : Program w CallType}
    {condition : Reg} {T : Nat} {D M : Int}
    (hy : Triple cost tape library (fun state => P state ∧ state.regs condition ≠ 0) yes Q T D M)
    (hn : Triple cost tape library (fun state => P state ∧ state.regs condition = 0) no Q T D M) :
    Triple cost tape library P (.branch condition yes no) Q (cost.branch + T) D M :=
  Caliper.Triple.ifNZ hy hn

theorem Triple.loop {I J : Nat → State w → Prop} {guard body : Program w CallType}
    {condition : Reg} {Tg Tb : Nat} {Dg Mg Db Mb : Int}
    (hg : ∀ k, Triple cost tape library (I k) guard (J k) Tg Dg Mg)
    (hpos : ∀ k state, J k state → state.regs condition ≠ 0 → ∃ k', k = k' + 1)
    (hb : ∀ k, Triple cost tape library (fun state => J (k + 1) state ∧ state.regs condition ≠ 0)
      body (I k) Tb Db Mb) (k : Nat) :
    Triple cost tape library (I k) (.loop guard condition body)
      (fun state => ∃ remaining, J remaining state ∧ state.regs condition = 0)
      ((k + 1) * (Tg + cost.branch) + k * Tb)
      (Dg + k * max (Dg + Db) 0)
      (max Mg (Dg + Mb) + k * max (Dg + Db) 0) :=
  Caliper.Triple.whileNZ_measure hg hpos hb k

variable {F G₁ G₂ : Type}
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]

/-- Calls contribute their proved time and workspace; framing and the operation's
mathematical specification establish the caller's chosen postcondition. -/
theorem CertifiedLibrary.call_triple {representations : Representations w F G₁ G₂}
    (library : CertifiedLibrary cost representations) (call : Call)
    {P Q : State w → Prop}
    (ready : ∀ before, P before → call.Ready representations (library call).scratch before)
    (post : ∀ before after, P before → call.Correct representations before after →
      call.Frame representations (library call).scratch before after → Q after) :
    Triple cost tape library.implementation P (.call call) Q
      (library call).time 0 (library call).workspace := by
  intro before hp
  obtain ⟨after, elapsed, net, peak, execution, correct, frame, ht, hd, hm⟩ :=
    library.call_exec call tape before (ready before hp)
  exact ⟨after, elapsed, net, peak, execution, post before after hp correct frame,
    ht, le_of_eq hd, hm⟩

end Signatures.Runtime.CaliperBackend
