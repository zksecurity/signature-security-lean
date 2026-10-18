import Signatures.Runtime.Caliper.WordPort

/-! Executable semantics for the word I/O boundary. Fuel limits each embedded
Caliper evaluation; the I/O syntax itself is finite. The interpreter never
decodes a mathematical value or invokes a host implementation of local work.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

structure Result (w : Nat) where
  state : State w
  time : Nat
  net : Int
  peak : Int
  trace : List (Event w)
  remaining : List (Word w)

def run (cost : Costs) (tape : RandomTape w) (fuel : Nat) :
    Code w → State w → List (Word w) → Option (Result w)
  | .compute code, before, input => do
      let (after, time, net, peak) ← Caliper.run cost.machine tape fuel code before
      pure ⟨after, time, net, peak, [], input⟩
  | .read destination, before, input => match input with
      | [] => none
      | value :: rest => some ⟨before.setReg destination value, cost.read, 0, 0, [.input value], rest⟩
  | .write source, before, input => some ⟨before, cost.write, 0, 0, [.output (before.regs source)], input⟩
  | .invoke, before, input => some ⟨before, cost.invoke, 0, 0, [.invoke], input⟩
  | .seq first second, before, input => do
      let left ← run cost tape fuel first before input
      let right ← run cost tape fuel second left.state left.remaining
      pure ⟨right.state, left.time + right.time, left.net + right.net,
        max left.peak (left.net + right.peak), left.trace ++ right.trace, right.remaining⟩
  | .branch condition yes no, before, input => do
      let result ← if before.regs condition = 0 then run cost tape fuel no before input
        else run cost tape fuel yes before input
      pure { result with time := cost.machine.branch + result.time }

theorem run_sound (cost : Costs) (tape : RandomTape w) (fuel : Nat) (code : Code w)
    (before : State w) (input : List (Word w)) (result : Result w)
    (success : run cost tape fuel code before input = some result) :
    Exec cost tape code before result.state result.trace result.time result.net result.peak := by
  induction code generalizing before input result with
  | compute code =>
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨⟨after, time, net, peak⟩, execution, equal⟩ := success
    cases equal
    exact Exec.compute (Caliper.run_sound fuel code execution)
  | read destination =>
    cases input with
    | nil => cases success
    | cons value rest => cases success; exact Exec.read
  | write source => cases success; exact Exec.write
  | invoke => cases success; exact Exec.invoke
  | seq first second ih₁ ih₂ =>
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
    obtain ⟨left, hleft, right, hright, equal⟩ := success
    cases equal
    exact Exec.seq (ih₁ _ _ _ hleft) (ih₂ _ _ _ hright)
  | branch condition yes no ihy ihn =>
    by_cases zero : before.regs condition = 0
    · simp only [run, zero, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨result, hresult, equal⟩ := success
      cases equal
      exact Exec.branch_no zero (ihn _ _ _ hresult)
    · simp only [run, zero, ite_false, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
      obtain ⟨result, hresult, equal⟩ := success
      cases equal
      exact Exec.branch_yes zero (ihy _ _ _ hresult)

def inputs : List (Event w) → List (Word w)
  | [] => []
  | .input value :: rest => value :: inputs rest
  | .output _ :: rest | .invoke :: rest => inputs rest

theorem inputs_append (left right : List (Event w)) : inputs (left ++ right) = inputs left ++ inputs right := by
  induction left with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [inputs, ih]

/-- Every operational execution is returned by the interpreter at sufficient
fuel. Only the trace's input words are supplied; no result state is installed. -/
theorem Exec.run_eventually {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape code before after trace time net peak) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ suffix,
      run cost tape fuel code before (inputs trace ++ suffix) =
        some ⟨after, time, net, peak, trace, suffix⟩ := by
  induction execution with
  | compute execution =>
    obtain ⟨bound, complete⟩ := execution.run_eventually
    exact ⟨bound, fun fuel enough suffix => by simp [run, inputs, complete fuel enough]⟩
  | read => exact ⟨0, fun _ _ _ => rfl⟩
  | write | invoke => exact ⟨0, fun _ _ _ => rfl⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨left, completeLeft⟩ := ih₁
    obtain ⟨right, completeRight⟩ := ih₂
    refine ⟨max left right, ?_⟩
    intro fuel enough suffix
    simp [run, inputs_append, List.append_assoc, completeLeft fuel (by omega), completeRight fuel (by omega)]
  | branch_yes nonzero _ ih =>
    obtain ⟨bound, complete⟩ := ih
    refine ⟨bound, fun fuel enough suffix => ?_⟩
    simp only [run, ite_eq_right nonzero, complete fuel enough suffix, Option.bind_eq_bind, Option.bind_some]
    rfl
  | branch_no zero _ ih =>
    obtain ⟨bound, complete⟩ := ih
    exact ⟨bound, fun fuel enough suffix => by simp [run, zero, complete fuel enough suffix]⟩

end Signatures.Runtime.CaliperBackend.WordIO
