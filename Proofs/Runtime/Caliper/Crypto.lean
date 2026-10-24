import Proofs.Runtime.Caliper.Encoding
import Proofs.Runtime.Arithmetic

/-! A finite cryptographic call interface over ordinary Caliper word storage.
The scalar/group operations have mathematical specifications. Each library
instance must supply Caliper code implementing them, with its own frame and
resource proofs. No generic function-call constructor is admitted.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

inductive ValueKind where
  | scalar | point₁ | point₂ | boolean
  deriving DecidableEq, Repr

abbrev ValueKind.Value (F G₁ G₂ : Type) : ValueKind → Type
  | .scalar => F
  | .point₁ => G₁
  | .point₂ => G₂
  | .boolean => Bool

abbrev Location : ValueKind → Type
  | .scalar | .point₁ | .point₂ => Address
  | .boolean => Reg

structure Representations (w : Nat) (F G₁ G₂ : Type) where
  scalar : Encoding w F
  point₁ : Encoding w G₁
  point₂ : Encoding w G₂
  scalar_fits : scalar.words < 2 ^ w
  point₁_fits : point₁.words < 2 ^ w
  point₂_fits : point₂.words < 2 ^ w

variable {w : Nat} {F G₁ G₂ : Type}

def Representations.At (representations : Representations w F G₁ G₂) :
    (sort : ValueKind) → Location sort → State w → sort.Value F G₁ G₂ → Prop
  | .scalar => representations.scalar.At
  | .point₁ => representations.point₁.At
  | .point₂ => representations.point₂.At
  | .boolean => BooleanAt

/-- The permitted external operations. Arithmetic on counters, bit inspection,
memory access and control flow are ordinary Caliper instructions. -/
inductive Operation : List ValueKind → ValueKind → Type
  | zero : Operation [] .scalar
  | one : Operation [] .scalar
  | add : Operation [.scalar, .scalar] .scalar
  | sub : Operation [.scalar, .scalar] .scalar
  | mul : Operation [.scalar, .scalar] .scalar
  | div : Operation [.scalar, .scalar] .scalar
  | neg : Operation [.scalar] .scalar
  | zero₁ : Operation [] .point₁
  | add₁ : Operation [.point₁, .point₁] .point₁
  | sub₁ : Operation [.point₁, .point₁] .point₁
  | scale₁ : Operation [.scalar, .point₁] .point₁
  | zero₂ : Operation [] .point₂
  | add₂ : Operation [.point₂, .point₂] .point₂
  | sub₂ : Operation [.point₂, .point₂] .point₂
  | scale₂ : Operation [.scalar, .point₂] .point₂
  | scalarEq : Operation [.scalar, .scalar] .boolean
  | point₁Eq : Operation [.point₁, .point₁] .boolean
  | point₂Eq : Operation [.point₂, .point₂] .boolean

abbrev Values (F G₁ G₂ : Type) : List ValueKind → Type
  | [] => Unit
  | sort :: rest => sort.Value F G₁ G₂ × Values F G₁ G₂ rest

abbrev Locations : List ValueKind → Type
  | [] => Unit
  | sort :: rest => Location sort × Locations rest

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]

def Operation.eval {inputs : List ValueKind} {output : ValueKind} :
    Operation inputs output → Values F G₁ G₂ inputs → output.Value F G₁ G₂
  | .zero, _ => 0
  | .one, _ => 1
  | .add, (x, y, ()) => x + y
  | .sub, (x, y, ()) => x - y
  | .mul, (x, y, ()) => x * y
  | .div, (x, y, ()) => x / y
  | .neg, (x, ()) => -x
  | .zero₁, _ => 0
  | .add₁, (x, y, ()) => x + y
  | .sub₁, (x, y, ()) => x - y
  | .scale₁, (x, y, ()) => x • y
  | .zero₂, _ => 0
  | .add₂, (x, y, ()) => x + y
  | .sub₂, (x, y, ()) => x - y
  | .scale₂, (x, y, ()) => x • y
  | .scalarEq, (x, y, ()) => decide (x = y)
  | .point₁Eq, (x, y, ()) => decide (x = y)
  | .point₂Eq, (x, y, ()) => decide (x = y)

def InputsAt (representations : Representations w F G₁ G₂) :
    (sorts : List ValueKind) → Locations sorts → State w → Values F G₁ G₂ sorts → Prop
  | [], (), _, () => True
  | sort :: rest, (address, addresses), state, (value, values) =>
      representations.At sort address state value ∧ InputsAt representations rest addresses state values

/-- A call names only a permitted operation and its encoded operands. -/
structure Call where
  inputs : List ValueKind
  output : ValueKind
  operation : Operation inputs output
  arguments : Locations inputs
  result : Location output

/-- Input interpretation and the required output. Preservation of unrelated
state and scratch-storage bounds are supplied by the routine contract. -/
def Call.Correct (representations : Representations w F G₁ G₂) (call : Call)
    (before after : State w) : Prop :=
  ∀ values, InputsAt representations call.inputs call.arguments before values →
    representations.At call.output call.result after (call.operation.eval values)

end Signatures.Runtime.CaliperBackend
