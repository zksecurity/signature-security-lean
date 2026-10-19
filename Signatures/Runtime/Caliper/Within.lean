import Signatures.Runtime.Caliper.InteractiveMemory
import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.BoundedSource

/-! Resource classes for actual Caliper programs, with pinned layouts and oracle
port. One stored program implements the algorithm on every represented input.
Private sampling uses the port; correctness and resource bounds hold for every
local tape, so an arbitrary tape cannot supply uncharged advice. Memory includes
stored code, dense register/descriptor reservations and every live buffer at
every visited instruction boundary. Input loading is a boundary convention;
its words are included in memory. Flat-memory/CPU adequacy remains separate. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {A B I : Type} {spec : OracleSpec I}

theorem Representation.initial_registers (input : Representation w A) (value : A) :
    RegisterBound (input.initial value) 0 := fun _ _ => rfl

theorem Representation.initial_buffers (input : Representation w A) (value : A) :
    (input.initial value).SupportBound 1 := by
  intro buffer outside
  simp [Representation.initial, show buffer ≠ 0 by omega]

theorem Representation.initial_memory (input : Representation w A) (value : A) :
    (input.initial value).liveMem 1 = input.encoding.words := by
  simp [State.liveMem, Representation.initial]

namespace Interactive
variable (port : Port w spec) (input : Layout w A) (output : Layout w B)

/-- Exact source semantics and complete resource bounds in one fixed word
machine. The quantified code is literal Caliper plus the fixed query protocol;
neither a host callback nor a solver-specific cost model is permitted. -/
def Within (words memory time : Nat) (algorithm : input.Value → OracleComp spec B) : Prop :=
  ∃ code : Code w,
    (code.lower port).DescriptionFits ∧ (code.lower port).descriptionWords ≤ words ∧
    (∀ tape value, (fun result => Subtype.val <$> observe output.representation result) <$>
        code.execute port .unit tape (input.representation.initial value) = some <$> algorithm value) ∧
    ∀ tape value finished, some finished ∈ support (code.execute port .unit tape (input.representation.initial value)) →
      finished.time ≤ time ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower port) (input.representation.initial value)
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (code.lower port).registerSlots ∧
          between.SupportBound (max 1 (code.lower port).memBound) ∧ between.WellFormed ∧
          ((code.lower port).staticWords 0 1 : Int) + between.liveMem (max 1 (code.lower port).memBound) ≤ memory

variable {port input output} {words memory time words' memory' time' : Nat}
    {algorithm other : input.Value → OracleComp spec B}

theorem Within.mono (bounded : Within port input output words memory time algorithm)
    (stored : words ≤ words') (space : memory ≤ memory') (elapsed : time ≤ time') :
    Within port input output words' memory' time' algorithm := by
  obtain ⟨code, fits, size, semantics, resources⟩ := bounded
  refine ⟨code, fits, size.trans stored, semantics, ?_⟩
  intro tape value finished reached
  obtain ⟨timed, execution, bounded⟩ := resources tape value finished reached
  refine ⟨timed.trans elapsed, execution, ?_⟩
  intro between visited
  obtain ⟨registers, buffers, formed, used⟩ := bounded between visited
  exact ⟨registers, buffers, formed, used.trans (by exact_mod_cast space)⟩

theorem Within.congr (bounded : Within port input output words memory time algorithm)
    (same : ∀ value, algorithm value = other value) : Within port input output words memory time other := by
  obtain ⟨code, fits, stored, semantics, resources⟩ := bounded
  exact ⟨code, fits, stored, fun tape value => (semantics tape value).trans (congrArg (fun computation => some <$> computation) (same value)), resources⟩

/-- Even a zero-step computation must account for its initial data. Exact source
semantics supplies a real supported run, so a failing executable cannot evade
the memory condition by having no successful executions. -/
theorem Within.input_memory_le (bounded : Within port input output words memory time algorithm)
    (value : input.Value) (answer : B) (supported : answer ∈ support (algorithm value)) :
    input.representation.encoding.words ≤ memory := by
  obtain ⟨code, _, _, semantics, resources⟩ := bounded
  have reached : some answer ∈ support ((fun result => Subtype.val <$> observe output.representation result) <$>
      code.execute port .unit RandomTape.zero (input.representation.initial value)) := by
    rw [semantics, support_map, Set.mem_image]
    exact ⟨answer, supported, rfl⟩
  rw [support_map, Set.mem_image] at reached
  obtain ⟨result, reached, observed⟩ := reached
  cases result with
  | none => cases observed
  | some finished =>
    obtain ⟨_, execution, bounded⟩ := resources RandomTape.zero value finished reached
    have used := (bounded (input.representation.initial value) (.start execution)).2.2.2
    have initialMemory := liveMem_eq_of_supportBound (input.representation.initial_buffers value)
      (Nat.le_max_left 1 (code.lower port).memBound)
    rw [initialMemory, input.representation.initial_memory] at used
    omega

/-- A proved local refinement and actual code/name/time bounds construct the
resource witness. The extra three words reserve the initial buffer descriptor. -/
theorem within_of_refines {code : Code w} {source : input.Value → OracleComp spec output.Value} {slots : Nat}
    (refined : Refines port .unit input.representation output.representation source code)
    (timed : TimeBound port .unit input.representation code time)
    (stored : (code.lower port).descriptionWords ≤ words)
    (named : WordIO.NamesBound (code.lower port) slots)
    (fits : (code.lower port).DescriptionFits) :
    Within port input output words (words + 4 * slots + 3 + input.representation.encoding.words + time) time
      (fun value => Subtype.val <$> source value) := by
  refine ⟨code, fits, stored, ?_, ?_⟩
  · intro tape value
    have observed := refined.observe tape value (input.representation.initial value) (input.representation.initial_holds value)
    have erased := congrArg (fun computation => (fun result => Subtype.val <$> result) <$> computation) observed
    have middle : (fun answer => Subtype.val <$> answer) <$> some <$> source value = some <$> Subtype.val <$> source value :=
      (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
    exact (PFunctor.FreeM.comp_map _ _ _).trans (erased.trans middle)
  · intro tape value finished reached
    obtain ⟨elapsed, _, _, _, execution, bounded⟩ := refined.resources timed stored named
      tape value (input.representation.initial value) (input.representation.initial_holds value) 0 1
      (input.representation.initial_registers value) (input.representation.initial_buffers value) finished reached
    refine ⟨elapsed, execution, ?_⟩
    intro between visited
    obtain ⟨registers, buffers, formed, used⟩ := bounded between visited
    refine ⟨by simpa only [Nat.zero_max] using registers, buffers, formed, ?_⟩
    rw [input.representation.initial_memory] at used
    push_cast
    omega

theorem within_of_refines_accounted {code : Code w} {source : input.Value → OracleComp spec output.Value} {slots : Nat}
    (refined : Refines port .unit input.representation output.representation source code)
    (timed : TimeBound port .unit input.representation code time)
    (stored : (code.lower port).descriptionWords ≤ words)
    (named : WordIO.NamesAccounted (code.lower port) slots)
    (fits : (code.lower port).DescriptionFits) :
    Within port input output words (5 * words + 4 * slots + 3 + input.representation.encoding.words + time) time
      (fun value => Subtype.val <$> source value) := by
  apply (within_of_refines refined timed stored
    ⟨named.registers.trans (Nat.add_le_add_left stored _), named.buffers.trans (Nat.add_le_add_left stored _)⟩ fits).mono le_rfl _ le_rfl
  omega
end Interactive
end Signatures.Runtime.CaliperBackend
