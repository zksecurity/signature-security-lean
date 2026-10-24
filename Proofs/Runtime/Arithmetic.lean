import Proofs.Runtime.Program
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs

/-! A fixed arithmetic instruction set. There is deliberately no instruction for evaluating an
arbitrary Lean function, a whole reduction, or a whole adversary. Costs name explicit primitive
contracts; they do not assert that an arbitrary `Field` or `Module` instance has that bit cost. -/

namespace Signatures.Runtime

inductive CryptoAtom where
  | scalar | point₁ | point₂ | key | message
  | fin (bound : Nat)

@[reducible] def cryptoBase (F G₁ G₂ K M : Type) : CryptoAtom → Type
  | .scalar => F
  | .point₁ => G₁
  | .point₂ => G₂
  | .key => K
  | .message => M
  | .fin n => Fin (n + 1)

abbrev scalar : Ty CryptoAtom := .atom .scalar
abbrev point₁ : Ty CryptoAtom := .atom .point₁
abbrev point₂ : Ty CryptoAtom := .atom .point₂
abbrev key : Ty CryptoAtom := .atom .key
abbrev message : Ty CryptoAtom := .atom .message
abbrev boundedNat (n : Nat) : Ty CryptoAtom := .atom (.fin n)

inductive CryptoOp : Ty CryptoAtom → Ty CryptoAtom → Type
  | zero : CryptoOp .unit scalar
  | one : CryptoOp .unit scalar
  | add : CryptoOp (.pair scalar scalar) scalar
  | sub : CryptoOp (.pair scalar scalar) scalar
  | mul : CryptoOp (.pair scalar scalar) scalar
  | div : CryptoOp (.pair scalar scalar) scalar
  | neg : CryptoOp scalar scalar
  | zero₁ : CryptoOp .unit point₁
  | add₁ : CryptoOp (.pair point₁ point₁) point₁
  | sub₁ : CryptoOp (.pair point₁ point₁) point₁
  | scale₁ : CryptoOp (.pair scalar point₁) point₁
  | scale₂ : CryptoOp (.pair scalar point₂) point₂
  | zero₂ : CryptoOp .unit point₂
  | add₂ : CryptoOp (.pair point₂ point₂) point₂
  | sub₂ : CryptoOp (.pair point₂ point₂) point₂
  | scalarEq : CryptoOp (.pair scalar scalar) .bool
  | point₁Eq : CryptoOp (.pair point₁ point₁) .bool
  | point₂Eq : CryptoOp (.pair point₂ point₂) .bool
  | keyEq : CryptoOp (.pair key key) .bool
  | messageEq : CryptoOp (.pair message message) .bool
  | natAdd : CryptoOp (.pair .nat .nat) .nat
  | natSub : CryptoOp (.pair .nat .nat) .nat
  | natEq : CryptoOp (.pair .nat .nat) .bool
  | natLt : CryptoOp (.pair .nat .nat) .bool
  | finVal (n : Nat) : CryptoOp (boundedNat n) .nat
  | finZero (n : Nat) : CryptoOp .unit (boundedNat n)
  | finOfNat (n : Nat) : CryptoOp .nat (boundedNat n)

structure PrimitiveCosts where
  field : Nat
  division : Nat
  group : Nat
  scalar₁ : Nat
  scalar₂ : Nat
  keyEq : Nat
  messageEq : Nat
  natOp : Nat
  scalarEq : Nat
  point₁Eq : Nat
  point₂Eq : Nat
  deriving Repr

def PrimitiveCosts.unit : PrimitiveCosts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

def CryptoOp.price (c : PrimitiveCosts) {a b : Ty CryptoAtom} : CryptoOp a b → Nat
  | .zero | .one | .add | .sub | .mul | .neg => c.field
  | .div => c.division
  | .zero₁ | .add₁ | .sub₁ | .zero₂ | .add₂ | .sub₂ => c.group
  | .scale₁ => c.scalar₁
  | .scale₂ => c.scalar₂
  | .keyEq => c.keyEq
  | .messageEq => c.messageEq
  | .scalarEq => c.scalarEq
  | .point₁Eq => c.point₁Eq
  | .point₂Eq => c.point₂Eq
  | .natAdd | .natSub | .natEq | .natLt => c.natOp
  | .finVal _ | .finZero _ | .finOfNat _ => c.natOp

def arithmetic (F G₁ G₂ K M : Type) [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
    [DecidableEq K] [DecidableEq M] (costs : PrimitiveCosts) :
    Primitives (cryptoBase F G₁ G₂ K M) CryptoOp where
  execute instr x := match instr with
    | .zero => 0
    | .one => 1
    | .add => x.1 + x.2
    | .sub => x.1 - x.2
    | .mul => x.1 * x.2
    | .div => x.1 / x.2
    | .neg => -x
    | .zero₁ => 0
    | .add₁ => x.1 + x.2
    | .sub₁ => x.1 - x.2
    | .scale₁ => x.1 • x.2
    | .scale₂ => x.1 • x.2
    | .zero₂ => 0
    | .add₂ => x.1 + x.2
    | .sub₂ => x.1 - x.2
    | .scalarEq => decide (x.1 = x.2)
    | .point₁Eq => decide (x.1 = x.2)
    | .point₂Eq => decide (x.1 = x.2)
    | .keyEq => decide (x.1 = x.2)
    | .messageEq => decide (x.1 = x.2)
    | .natAdd => x.1 + x.2
    | .natSub => x.1 - x.2
    | .natEq => decide (x.1 = x.2)
    | .natLt => decide (x.1 < x.2)
    | .finVal _ => x.val
    | .finZero _ => 0
    | .finOfNat n => ⟨x % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩
  cost instr _ := instr.price costs

end Signatures.Runtime
