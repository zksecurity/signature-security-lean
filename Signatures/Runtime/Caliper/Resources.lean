import Signatures.Runtime.Caliper.Realizer

/-! Resource consequences of actual Caliper execution. The dynamic profile
counts buffers; a conservative static register/descriptor reservation and stored
code are charged separately. This is a machine-level accounting convention, not
yet a refinement to a flat-memory allocator or physical CPU.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

/-- Dense register slots, including unused gaps between static names. This is
deliberately conservative and does not assume an unproved register allocator. -/
def registerSlots : Stmt w → Nat
  | .skip | .memAllocI .. | .memFree .. | .memPop .. => 0
  | .seq first second => max (registerSlots first) (registerSlots second)
  | .imm dst _ | .rand dst | .memLen dst _ => dst + 1
  | .mov dst src | .un _ dst src => max dst src + 1
  | .bin _ dst left right => max dst (max left right) + 1
  | .memAlloc _ size => size + 1
  | .memLoad dst _ index => max dst index + 1
  | .memStore _ index src => max index src + 1
  | .memPush _ src => src + 1
  | .ifNZ condition yes no => max (condition + 1) (max (registerSlots yes) (registerSlots no))
  | .whileNZ guard condition body =>
      max (condition + 1) (max (registerSlots guard) (registerSlots body))

def RegisterBound (state : State w) (slots : Nat) : Prop :=
  ∀ register, slots ≤ register → state.regs register = 0

theorem writes_lt_registerSlots {code : Stmt w} {register : Reg}
    (written : code.Writes register) : register < registerSlots code := by
  induction code with
  | seq first second ihf ihs =>
    rcases written with hf | hs
    · exact lt_of_lt_of_le (ihf hf) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihs hs) (le_max_right _ _)
  | ifNZ condition yes no ihy ihn =>
    rcases written with hy | hn
    · exact lt_of_lt_of_le (ihy hy) ((le_max_left _ _).trans (le_max_right _ _))
    · exact lt_of_lt_of_le (ihn hn) ((le_max_right _ _).trans (le_max_right _ _))
  | whileNZ guard condition body ihg ihb =>
    rcases written with hg | hb
    · exact lt_of_lt_of_le (ihg hg) ((le_max_left _ _).trans (le_max_right _ _))
    · exact lt_of_lt_of_le (ihb hb) ((le_max_right _ _).trans (le_max_right _ _))
  | _ => simp_all [Stmt.Writes, registerSlots]

theorem registerBound_preserved {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before after : State w} {time : Nat} {net peak : Int} {slots : Nat}
    (execution : Caliper.Exec cost tape code before after time net peak)
    (initial : RegisterBound before slots) :
    RegisterBound after (max slots (registerSlots code)) := by
  intro register hr
  have notWritten : ¬ code.Writes register := by
    intro written
    exact Nat.not_lt_of_ge ((le_max_right slots (registerSlots code)).trans hr)
      (writes_lt_registerSlots written)
  rw [execution.frame_reg notWritten]
  exact initial register (by omega)

/-- One pointer, length and capacity per buffer descriptor. Bounds reserve all
named slots; initial buffers/registers must be included in the chosen bounds. -/
def staticWords (code : Stmt w) (initialRegisterSlots initialBufferSlots : Nat) : Nat :=
  descriptionWords code + max initialRegisterSlots (registerSlots code) +
    3 * max initialBufferSlots code.memBound

theorem buffer_memory_bound {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before after : State w} {elapsed : Nat} {net peak : Int} {buffers : Nat}
    (execution : Caliper.Exec cost tape code before after elapsed net peak)
    (code_bound : code.memBound ≤ buffers) :
    (after.liveMem buffers : Int) ≤ before.liveMem buffers + peak :=
  execution.liveMem_le_peak (Stmt.touches_lt_of_memBound_le code_bound)

/-- The same bound covers every intermediate state, not just the final result.
Together with an initial support bound, these sums count all live buffers. -/
theorem intermediate_buffer_memory_bound {cost : CostModel} {tape : RandomTape w}
    {code : Stmt w} {before after between : State w} {elapsed : Nat} {net peak : Int}
    {buffers : Nat} (execution : Caliper.Exec cost tape code before after elapsed net peak)
    (reached : Caliper.Reaches cost tape code before between)
    (code_bound : code.memBound ≤ buffers) :
    (between.liveMem buffers : Int) ≤ before.liveMem buffers + peak :=
  execution.reaches_liveMem_le_peak reached (Stmt.touches_lt_of_memBound_le code_bound)

variable {A B : Type} {cost : CostModel} {input : Representation w A}
  {output : Representation w B} {f : A → B}

/-- A certified local map's workspace bound transfers to any actual run, by
determinism of Caliper; the two executions cannot assign different profiles. -/
theorem Realizer.execution_bounds (realizer : Realizer cost input output f)
    {tape : RandomTape w} {value : A} {before after : State w} {elapsed : Nat} {net peak : Int}
    (represented : input.Holds value before)
    (execution : Caliper.Exec cost tape realizer.code before after elapsed net peak) :
    output.Holds (f value) after ∧ elapsed = realizer.time value ∧
      net ≤ realizer.net value ∧ peak ≤ realizer.workspace value := by
  obtain ⟨after', net', peak', certified, hout, hn, hp⟩ :=
    realizer.correct tape value before represented
  obtain ⟨rfl, rfl, rfl, rfl⟩ := execution.deterministic certified
  exact ⟨hout, rfl, hn, hp⟩

theorem Realizer.total_memory_bound (realizer : Realizer cost input output f)
    {tape : RandomTape w} {value : A} {before after : State w} {elapsed : Nat} {net peak : Int}
    (represented : input.Holds value before)
    (execution : Caliper.Exec cost tape realizer.code before after elapsed net peak)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) :
    RegisterBound after (max registers (registerSlots realizer.code)) ∧
    after.SupportBound (max buffers realizer.code.memBound) ∧
    (staticWords realizer.code registers buffers : Int) +
        after.liveMem (max buffers realizer.code.memBound) ≤
      staticWords realizer.code registers buffers +
        before.liveMem (max buffers realizer.code.memBound) + realizer.workspace value := by
  refine ⟨registerBound_preserved execution initialRegisters,
    execution.supportBound_preserved
      (Stmt.touches_lt_of_memBound_le (le_max_right buffers realizer.code.memBound))
      (initialBuffers.mono (le_max_left buffers realizer.code.memBound)), ?_⟩
  have hmem := buffer_memory_bound execution (le_max_right buffers realizer.code.memBound)
  have hp := (realizer.execution_bounds represented execution).2.2.2
  omega

end Signatures.Runtime.CaliperBackend
