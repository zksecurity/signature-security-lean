import Proofs.Runtime.Caliper.Crypto
import Proofs.Runtime.Caliper.Description
import Caliper.Tape

/-! Contracts for separately verified cryptographic routines. These are local
implementation obligations, not axioms or assumptions that the finished reduction
is efficient. Results occupy preallocated storage; temporary buffers are returned
empty. Peak workspace includes every temporary allocation during execution.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {F G₁ G₂ : Type}

def Representations.words (representations : Representations w F G₁ G₂) : ValueKind → Nat
  | .scalar => representations.scalar.words
  | .point₁ => representations.point₁.words
  | .point₂ => representations.point₂.words
  | .boolean => 0

def Location.pointerRegisters : (kind : ValueKind) → Location kind → Finset Reg
  | .scalar, address | .point₁, address | .point₂, address => {address.offset}
  | .boolean, _ => ∅

def Location.buffers : (kind : ValueKind) → Location kind → Finset BufId
  | .scalar, address | .point₁, address | .point₂, address => {address.buffer}
  | .boolean, _ => ∅

def Location.NamesFit (w : Nat) : (kind : ValueKind) → Location kind → Prop
  | .scalar, address | .point₁, address | .point₂, address =>
      address.buffer < 2 ^ w ∧ address.offset < 2 ^ w
  | .boolean, register => register < 2 ^ w

def Location.Valid (words : Nat) : (kind : ValueKind) → Location kind → State w → Prop
  | .scalar, address, state | .point₁, address, state | .point₂, address, state =>
      Address.Valid address words state
  | .boolean, _, _ => True

def Locations.pointerRegisters : (kinds : List ValueKind) → Locations kinds → Finset Reg
  | [], () => ∅
  | kind :: rest, (location, locations) =>
      Location.pointerRegisters kind location ∪ Locations.pointerRegisters rest locations

def Locations.buffers : (kinds : List ValueKind) → Locations kinds → Finset BufId
  | [], () => ∅
  | kind :: rest, (location, locations) =>
      Location.buffers kind location ∪ Locations.buffers rest locations

def Locations.NamesFit (w : Nat) : (kinds : List ValueKind) → Locations kinds → Prop
  | [], () => True
  | kind :: rest, (location, locations) =>
      Location.NamesFit w kind location ∧ Locations.NamesFit w rest locations

structure Scratch where
  registers : Finset Reg
  buffers : Finset BufId

/-- Scratch cannot alias operand buffers or the registers holding their offsets.
Inputs and output may alias each other only when the implementation proves it safe. -/
def Call.Ready (representations : Representations w F G₁ G₂) (call : Call)
    (scratch : Scratch) (state : State w) : Prop :=
  state.WellFormed ∧ (∀ buffer, state.caps buffer < 2 ^ w) ∧
  Locations.NamesFit w call.inputs call.arguments ∧ Location.NamesFit w call.output call.result ∧
  (∀ register ∈ scratch.registers, register < 2 ^ w) ∧
  (∀ buffer ∈ scratch.buffers, buffer < 2 ^ w) ∧
  (∃ values, InputsAt representations call.inputs call.arguments state values) ∧
  Location.Valid (representations.words call.output) call.output call.result state ∧
  Disjoint scratch.registers (Locations.pointerRegisters call.inputs call.arguments ∪
    Location.pointerRegisters call.output call.result) ∧
  Disjoint scratch.buffers (Locations.buffers call.inputs call.arguments ∪
    Location.buffers call.output call.result) ∧
  (∀ buffer ∈ scratch.buffers, state.caps buffer = 0)

def Call.resultRegister (call : Call) : Finset Reg :=
  match call.output, call.result with
  | .boolean, register => {register}
  | .scalar, _ | .point₁, _ | .point₂, _ => ∅

/-- Exactly the output slice, measured in the pre-call state. -/
def Call.Writes (representations : Representations w F G₁ G₂) (call : Call)
    (before : State w) (buffer : BufId) (index : Nat) : Prop :=
  match call.output, call.result with
  | .boolean, _ => False
  | .scalar, address | .point₁, address | .point₂, address =>
      buffer = address.buffer ∧ address.start before ≤ index ∧
        index < address.start before + representations.words call.output

/-- Slice-level framing also protects unrelated values in the *same* buffer.
Scratch registers may change; temporary buffers must be released. -/
def Call.Frame (representations : Representations w F G₁ G₂) (call : Call)
    (scratch : Scratch) (before after : State w) : Prop :=
  (∀ register, register ∉ scratch.registers ∪ call.resultRegister →
    after.regs register = before.regs register) ∧
  (∀ buffer, after.caps buffer = before.caps buffer) ∧
  (∀ buffer, (after.bufs buffer).size = (before.bufs buffer).size) ∧
  (∀ buffer index, ¬ call.Writes representations before buffer index →
    (after.bufs buffer)[index]? = (before.bufs buffer)[index]?) ∧
  after.tapePos = before.tapePos

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]

/-- A real Caliper implementation and its explicit bounds. The mathematical
operation is a specification of this code, never an extra machine instruction. -/
structure Routine (cost : CostModel) (representations : Representations w F G₁ G₂)
    (call : Call) where
  code : Stmt w
  scratch : Scratch
  time : Nat
  workspace : Nat
  positive_width : 0 < w
  description_fits : DescriptionFits code
  random_free : code.RandomFree
  correct : ∀ tape before, call.Ready representations scratch before →
    ∃ after elapsed net peak,
      Caliper.Exec cost tape code before after elapsed net peak ∧
      call.Correct representations before after ∧
      call.Frame representations scratch before after ∧
      elapsed ≤ time ∧ net = 0 ∧ peak ≤ workspace

def Routine.descriptionWords {cost : CostModel} {representations : Representations w F G₁ G₂}
    {call : Call} (routine : Routine cost representations call) : Nat :=
  CaliperBackend.descriptionWords routine.code

/-- Choosing the library supplies routine code and proofs, separately from the
signature games and probability reductions. -/
abbrev CertifiedLibrary (cost : CostModel) (representations : Representations w F G₁ G₂) :=
  (call : Call) → Routine cost representations call

def CertifiedLibrary.implementation {cost : CostModel}
    {representations : Representations w F G₁ G₂}
    (library : CertifiedLibrary cost representations) : Library w Call :=
  fun call => (library call).code

theorem CertifiedLibrary.call_exec {cost : CostModel}
    {representations : Representations w F G₁ G₂}
    (library : CertifiedLibrary cost representations) (call : Call) (tape : RandomTape w)
    (before : State w) (ready : call.Ready representations (library call).scratch before) :
    ∃ after elapsed net peak,
      Exec cost tape library.implementation (.call call) before after elapsed net peak ∧
      call.Correct representations before after ∧
      call.Frame representations (library call).scratch before after ∧
      elapsed ≤ (library call).time ∧ net = 0 ∧ peak ≤ (library call).workspace :=
  (library call).correct tape before ready

end Signatures.Runtime.CaliperBackend
