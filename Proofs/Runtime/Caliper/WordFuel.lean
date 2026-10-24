import Proofs.Runtime.Caliper.WordRun

/-! Explicit interpreter fuel for the packet adapter. This is evaluator depth,
not the resource charge: executed instructions, allocation and I/O keep their
separate exact time and memory accounts.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

def straightFuel : Stmt w → Nat
  | .seq first second => max (straightFuel first) (straightFuel second) + 1
  | _ => 1

theorem run_straight {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before after : State w} {time : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape code before after time net peak) (straight : code.Straight)
    (fuel : Nat) (enough : straightFuel code ≤ fuel) :
    Caliper.run cost tape fuel code before = some (after, time, net, peak) := by
  induction execution generalizing fuel with
  | seq _ _ ih₁ ih₂ =>
    cases fuel with
    | zero => simp [straightFuel] at enough
    | succ fuel =>
      have left := ih₁ straight.1 fuel (by simp only [straightFuel] at enough; omega)
      have right := ih₂ straight.2 fuel (by simp only [straightFuel] at enough; omega)
      simp [Caliper.run, left, right]
  | _ => cases fuel <;> simp_all [straightFuel, Stmt.Straight, Caliper.run]

def Code.localFuel : Code w → Nat
  | .compute code => straightFuel code
  | .read _ | .write _ | .invoke => 0
  | .seq first second => max first.localFuel second.localFuel
  | .branch _ yes no => max yes.localFuel no.localFuel

def Code.StraightLocal : Code w → Prop
  | .compute code => code.Straight
  | .read _ | .write _ | .invoke => True
  | .seq first second => first.StraightLocal ∧ second.StraightLocal
  | .branch _ yes no => yes.StraightLocal ∧ no.StraightLocal

theorem Exec.run_atFuel {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak)
    (straight : code.StraightLocal) (fuel : Nat) (enough : code.localFuel ≤ fuel) (suffix : List (Word w)) :
    run cost tape fuel code before (inputs trace ++ suffix) =
      some ⟨after, time, net, peak, trace, suffix⟩ := by
  induction execution generalizing suffix with
  | compute execution => simp [run, inputs, run_straight execution straight fuel enough]
  | read | write | invoke => rfl
  | seq _ _ ih₁ ih₂ =>
    have left := ih₁ straight.1 (le_trans (le_max_left _ _) enough)
    have right := ih₂ straight.2 (le_trans (le_max_right _ _) enough)
    simp [run, inputs_append, List.append_assoc, left, right]
  | branch_yes nonzero _ ih =>
    simp only [run, ite_eq_right nonzero, ih straight.1 (le_trans (le_max_left _ _) enough) suffix,
      Option.bind_eq_bind, Option.bind_some]
    rfl
  | branch_no zero _ ih =>
    simp [run, zero, ih straight.2 (le_trans (le_max_right _ _) enough) suffix]

theorem send_fuel (buffer start count : Nat) :
    (send (w := w) buffer start count).localFuel ≤ 2 ∧ (send (w := w) buffer start count).StraightLocal := by
  induction count generalizing start <;>
    simp_all [send, Code.localFuel, Code.StraightLocal, straightFuel, Stmt.Straight]

theorem receive_fuel (buffer count : Nat) :
    (receive (w := w) buffer count).localFuel ≤ 1 ∧ (receive (w := w) buffer count).StraightLocal := by
  induction count <;> simp_all [receive, Code.localFuel, Code.StraightLocal, straightFuel, Stmt.Straight]

theorem exchange_fuel (requestWords replyWords : Nat) :
    (exchange (w := w) requestWords replyWords).localFuel ≤ 2 ∧
      (exchange (w := w) requestWords replyWords).StraightLocal := by
  have sending := send_fuel (w := w) 0 0 requestWords
  have receiving := receive_fuel (w := w) 0 replyWords
  simp only [exchange, Code.localFuel, Code.StraightLocal, straightFuel, Stmt.Straight, max_le_iff]
  exact ⟨⟨sending.1, by omega, by omega, by omega⟩, sending.2, trivial, trivial, receiving.2⟩

/-- The executable packet adapter returns the certified trace, encoded reply and
exact profile with one fixed local evaluation depth, for every represented input
and every represented reply. No unproved uniform termination bound is assumed. -/
theorem exchange_run {A B : Type} (cost : Costs) (tape : RandomTape w)
    (request : Representation w A) (reply : Representation w B) (value : A) (answer : B)
    (before : State w) (represented : request.Holds value before) (suffix : List (Word w)) :
    ∃ result, run cost tape 2 (exchange request.encoding.words reply.encoding.words) before
      (reply.encoding.encode answer ++ suffix) = some result ∧
      reply.Holds answer result.state ∧
      result.trace = (request.encoding.encode value).map Event.output ++ .invoke :: (reply.encoding.encode answer).map Event.input ∧
      result.time = exchangeTime cost request.encoding.words reply.encoding.words ∧
      result.net = (reply.encoding.words : Int) - before.caps 0 ∧
      result.peak = max ((reply.encoding.words : Int) - before.caps 0) 0 ∧ result.remaining = suffix := by
  obtain ⟨after, execution, result⟩ := exchange_exec cost tape request reply value answer before represented
  have hrun := execution.run_atFuel (exchange_fuel _ _).2 2 (exchange_fuel _ _).1 suffix
  have incoming (xs : List (Word w)) : inputs (xs.map Event.input) = xs := by
    induction xs <;> simp [inputs, *]
  have outgoing (xs : List (Word w)) : inputs (xs.map Event.output) = [] := by
    induction xs <;> simp [inputs, *]
  refine ⟨⟨after, exchangeTime cost request.encoding.words reply.encoding.words,
    (reply.encoding.words : Int) - before.caps 0, max ((reply.encoding.words : Int) - before.caps 0) 0,
    (request.encoding.encode value).map Event.output ++ .invoke :: (reply.encoding.encode answer).map Event.input,
    suffix⟩, ?_, result, rfl, rfl, rfl, rfl, rfl⟩
  simpa [inputs_append, inputs, incoming, outgoing] using hrun

end Signatures.Runtime.CaliperBackend.WordIO
