import Proofs.Runtime.Caliper.OracleCall
import Proofs.Runtime.Caliper.Synchronizes
import Caliper.Outcome

/-! Finite interactive target programs. Local blocks contain literal Caliper
statements; query nodes lower to the verified word packet adapter. Sequencing and
register branches contain no host callbacks. Their semantics execute actual
machine states and accumulate time, memory and I/O traces.

`outcome` is Caliper's observation of terminating execution, not a local machine
operation. Certified realizers establish termination on their represented domain.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper OracleComp OracleSpec

variable {w : Nat} {I : Type} {spec : OracleSpec I}

structure Port (w : Nat) (spec : OracleSpec I) where
  Request : Type
  source : Request → I
  request : Representation w Request
  reply : Representation w (Σ i, spec.Range (source i))

def Port.restricted (port : Port w spec) : OracleSpec port.Request := fun position => spec (port.source position)

/-- A port may represent a bounded subset of an unbounded source interface, such
as uniform sampling requests whose modulus fits the selected word width. -/
def Port.call (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w) (before : State w) :
    OracleComp spec (Option (WordIO.Result w)) :=
  simulateQ (fun position => queryBind (port.source position) Pure.pure)
    (WordIO.oracleCall port.restricted cost tape port.request port.reply before)

theorem Port.call_eq (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    (position : port.Request) (before : State w) (represented : port.request.Holds position before) :
    port.call cost tape before = queryBind (port.source position) (fun answer =>
      pure (WordIO.run cost tape 2 (WordIO.exchange port.request.encoding.words port.reply.encoding.words) before
        (port.reply.encoding.encode ⟨position, answer⟩))) := by
  rw [Port.call, WordIO.oracleCall_eq port.restricted cost tape port.request port.reply position before represented]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rfl

inductive Code (w : Nat) where
  | compute (code : Stmt w)
  | query
  | seq (first second : Code w)
  | branch (condition : Reg) (yes no : Code w)

def Code.lower (port : Port w spec) : Code w → WordIO.Code w
  | .compute code => .compute code
  | .query => WordIO.exchange port.request.encoding.words port.reply.encoding.words
  | .seq first second => .seq (first.lower port) (second.lower port)
  | .branch condition yes no => .branch condition (yes.lower port) (no.lower port)

def join (left right : WordIO.Result w) : WordIO.Result w :=
  ⟨right.state, left.time + right.time, left.net + right.net,
    max left.peak (left.net + right.peak), left.trace ++ right.trace, right.remaining⟩

def ofOutcome (result : Caliper.Outcome w) : WordIO.Result w :=
  ⟨result.1, result.2.1, result.2.2.1, result.2.2.2, [], []⟩

noncomputable def Code.execute (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w) :
    Code w → State w → OracleComp spec (Option (WordIO.Result w))
  | .compute code, before => pure (ofOutcome <$> Caliper.outcome cost.machine code before tape)
  | .query, before => port.call cost tape before
  | .seq first second, before => do
      match ← first.execute port cost tape before with
      | none => pure none
      | some left => (fun right => join left <$> right) <$> second.execute port cost tape left.state
  | .branch condition yes no, before =>
      (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) <$>
        (if before.regs condition = 0 then no.execute port cost tape before else yes.execute port cost tape before)

/-- A local correctness proof determines exactly the result observed by the
interactive semantics, including its real execution profile. -/
theorem execute_of_exec (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    {code : Stmt w} {before after : State w} {time : Nat} {net peak : Int}
    (execution : Caliper.Exec cost.machine tape code before after time net peak) :
    Code.execute port cost tape (.compute code) before =
      pure (some ⟨after, time, net, peak, [], []⟩) := by
  have observed := Caliper.outcome_of_exec (r := (after, time, net, peak)) execution
  simp [Code.execute, observed, ofOutcome]

/-- Typed observations are specifications. The target program accesses the
encoded bytes through Caliper instructions, not through this decoder. -/
def observe {A : Type} (representation : Representation w A) (result : Option (WordIO.Result w)) : Option A :=
  result.bind fun finished => representation.encoding.decode (finished.state.bufs 0).toList

def Represents {A : Type} (representation : Representation w A)
    (cost : WordIO.Costs) (tape : RandomTape w) (code : WordIO.Code w) (before : State w) (value : A)
    (result : Option (WordIO.Result w)) : Prop :=
  ∃ finished, result = some finished ∧ representation.Holds value finished.state ∧ finished.remaining = [] ∧
    WordIO.Exec cost tape code before finished.state finished.trace finished.time finished.net finished.peak

theorem Represents.observe {A : Type} {representation : Representation w A} {value : A}
    {cost : WordIO.Costs} {tape : RandomTape w} {code : WordIO.Code w} {before : State w}
    {result : Option (WordIO.Result w)} (represented : Represents representation cost tape code before value result) :
    Interactive.observe representation result = some value := by
  obtain ⟨finished, rfl, holds, _, _⟩ := represented
  simp [Interactive.observe, holds.2.1, representation.encoding.decode_encode]

/-- Source-to-target refinement keeps the state invariant at every returned
branch, allowing the following component to execute on actual machine memory. -/
def Refines {A B : Type} (port : Port w spec) (cost : WordIO.Costs)
    (input : Representation w A) (output : Representation w B)
    (source : A → OracleComp spec B) (target : Code w) : Prop :=
  ∀ tape value before, input.Holds value before →
    Synchronizes (Represents output cost tape (target.lower port) before) (source value) (target.execute port cost tape before)

theorem Refines.observe {A B : Type} {port : Port w spec} {cost : WordIO.Costs}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refines : Refines port cost input output source target)
    (tape : RandomTape w) (value : A) (before : State w) (represented : input.Holds value before) :
    Interactive.observe output <$> target.execute port cost tape before = some <$> source value :=
  ((refines tape value before represented).map_eq some (Interactive.observe output)
    (fun _ _ h => h.observe.symm)).symm

theorem Refines.compute {A B : Type} (port : Port w spec) (cost : WordIO.Costs)
    {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer cost.machine input output f) :
    Refines port cost input output (fun value => pure (f value)) (.compute body.code) := by
  intro tape value before represented
  obtain ⟨after, net, peak, execution, result, _, _⟩ := body.correct tape value before represented
  rw [execute_of_exec port cost tape execution]
  exact .pure ⟨⟨after, body.time value, net, peak, [], []⟩, rfl, result, rfl, .compute execution⟩

theorem Refines.query (port : Port w spec) (cost : WordIO.Costs) :
    Refines port cost port.request port.reply
      (fun position => queryBind (port.source position) (fun answer => pure (Sigma.mk position answer))) .query := by
  intro tape position before represented
  rw [Code.execute, port.call_eq cost tape position before represented]
  apply Synchronizes.query (port.source position)
  intro answer
  obtain ⟨result, execution, holds, _, _, _, _, remaining⟩ :=
    WordIO.exchange_run cost tape port.request port.reply position ⟨position, answer⟩ before represented []
  simp only [List.append_nil] at execution
  rw [execution]
  exact .pure ⟨result, rfl, holds, remaining, WordIO.run_sound _ _ _ _ _ _ _ execution⟩

theorem Refines.seq {A B D : Type} {port : Port w spec} {cost : WordIO.Costs}
    {input : Representation w A} {middle : Representation w B} {output : Representation w D}
    {f : A → OracleComp spec B} {g : B → OracleComp spec D} {first second : Code w}
    (firstRefines : Refines port cost input middle f first)
    (secondRefines : Refines port cost middle output g second) :
    Refines port cost input output (fun value => f value >>= g) (.seq first second) := by
  intro tape value before represented
  apply (firstRefines tape value before represented).bind g
    (fun result => match result with
      | none => pure none
      | some left => (fun right => join left <$> right) <$> second.execute port cost tape left.state)
  intro intermediate result related
  obtain ⟨left, rfl, holds, _, leftExec⟩ := related
  have next := secondRefines tape intermediate left.state holds
  simpa using next.map id (fun result => join left <$> result) (by
    intro value result related
    obtain ⟨right, rfl, holds, remaining, rightExec⟩ := related
    exact ⟨join left right, rfl, holds, remaining, .seq leftExec rightExec⟩)

/-- Change the mathematical output view only after proving identical encodings.
The target code and its execution profile are unchanged. -/
theorem Refines.viewOutput {A B D : Type} {port : Port w spec} {cost : WordIO.Costs}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refines : Refines port cost input output source target)
    (newOutput : Representation w D) (view : B → D)
    (sameBytes : ∀ value, newOutput.encoding.encode (view value) = output.encoding.encode value) :
    Refines port cost input newOutput (fun value => view <$> source value) target := by
  intro tape value before represented
  simpa only [id_map] using (refines tape value before represented).map view id (by
    intro answer result realization
    obtain ⟨finished, rfl, holds, remaining, execution⟩ := realization
    exact ⟨finished, rfl, ⟨holds.1, holds.2.1.trans (sameBytes answer).symm, holds.2.2⟩, remaining, execution⟩)

theorem Refines.viewInput {A B D : Type} {port : Port w spec} {cost : WordIO.Costs}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {target : Code w}
    (refines : Refines port cost input output source target)
    (newInput : Representation w D) (view : D → A)
    (sameBytes : ∀ value, input.encoding.encode (view value) = newInput.encoding.encode value) :
    Refines port cost newInput output (fun value => source (view value)) target := by
  intro tape value before represented
  exact refines tape (view value) before
    ⟨represented.1, represented.2.1.trans (sameBytes value).symm, represented.2.2⟩

end Signatures.Runtime.CaliperBackend.Interactive
