import Signatures.Runtime.Language
import Mathlib.Data.List.GetD

/-! Self-delimiting heap nodes on a bit tape. Addresses count nodes, not bytes:
using unary byte offsets inside variable-sized nodes can grow exponentially.
All online encoding/decoding traversals below carry cell-step counts. -/

namespace Signatures.Runtime.HeapBits

abbrev Address := List Unit

inductive Node where
  | word (bits : List Bool)
  | pair (left right : Address)
  | nil
  | cons (head tail : Address)
  deriving DecidableEq, Repr

def unary {A : Type} : List A → List Bool
  | [] => [false]
  | _ :: xs => true :: unary xs

theorem unary_length {A : Type} (xs : List A) : (unary xs).length = xs.length + 1 := by
  induction xs <;> simp [unary, *]

def Node.bits : Node → List Bool
  | .word xs => false :: false :: (unary xs ++ xs)
  | .pair a b => false :: true :: (unary a ++ unary b)
  | .nil => [true, false]
  | .cons a b => true :: true :: (unary a ++ unary b)

def copy {A : Type} : List A → Run (List A)
  | [] => ⟨[], 1⟩
  | x :: xs => let r := copy xs; ⟨x :: r.value, r.steps + 2⟩

def append {A : Type} : List A → List A → Run (List A)
  | [], ys => ⟨ys, 1⟩
  | x :: xs, ys => let r := append xs ys; ⟨x :: r.value, r.steps + 2⟩

def emitUnary {A : Type} : List A → Run (List Bool)
  | [] => ⟨[false], 1⟩
  | _ :: xs => let r := emitUnary xs; ⟨true :: r.value, r.steps + 2⟩

theorem copy_value {A : Type} (xs : List A) : (copy xs).value = xs := by
  induction xs <;> simp [copy, *]

theorem copy_steps {A : Type} (xs : List A) : (copy xs).steps = 2*xs.length + 1 := by
  induction xs <;> simp [copy, *]
  omega

theorem append_value {A : Type} (xs ys : List A) : (append xs ys).value = xs ++ ys := by
  induction xs <;> simp [append, *]

theorem append_steps {A : Type} (xs ys : List A) : (append xs ys).steps = 2*xs.length + 1 := by
  induction xs <;> simp [append, *]
  omega

theorem emitUnary_value {A : Type} (xs : List A) : (emitUnary xs).value = unary xs := by
  induction xs <;> simp [emitUnary, unary, *]

theorem emitUnary_steps {A : Type} (xs : List A) : (emitUnary xs).steps = 2*xs.length + 1 := by
  induction xs <;> simp [emitUnary, *]
  omega

private def encodeLinks (tag : Bool) (a b : Address) : Run (List Bool) :=
  let left := emitUnary a
  let right := emitUnary b
  let out := append left.value right.value
  ⟨tag :: true :: out.value, left.steps + right.steps + out.steps + 2⟩

def encodeNode : Node → Run (List Bool)
  | .word xs =>
    let n := emitUnary xs
    let data := copy xs
    let out := append n.value data.value
    ⟨false :: false :: out.value, n.steps + data.steps + out.steps + 2⟩
  | .pair a b => encodeLinks false a b
  | .cons a b => encodeLinks true a b
  | .nil => ⟨[true, false], 3⟩

theorem encodeNode_value (n : Node) : (encodeNode n).value = n.bits := by
  cases n <;> simp [encodeNode, encodeLinks, Node.bits, emitUnary_value, copy_value, append_value]

theorem encodeNode_steps (n : Node) : (encodeNode n).steps ≤ 4*n.bits.length + 3 := by
  cases n <;>
    simp [encodeNode, encodeLinks, Node.bits, emitUnary_steps, copy_steps, append_steps,
      emitUnary_value, unary_length] <;> omega

def readUnary : List Bool → Run (Option (Address × List Bool))
  | [] => ⟨none, 1⟩
  | false :: rest => ⟨some ([], rest), 2⟩
  | true :: rest =>
    let r := readUnary rest
    ⟨r.value.map (fun p => (() :: p.1, p.2)), r.steps + 3⟩

def takeWord : Address → List Bool → Run (Option (List Bool × List Bool))
  | [], rest => ⟨some ([], rest), 1⟩
  | _ :: _, [] => ⟨none, 1⟩
  | _ :: n, b :: rest =>
    let r := takeWord n rest
    ⟨r.value.map (fun p => (b :: p.1, p.2)), r.steps + 3⟩

theorem readUnary_value {A : Type} (xs : List A) (rest : List Bool) :
    (readUnary (unary xs ++ rest)).value = some (xs.map (fun _ => ()), rest) := by
  induction xs <;> simp [unary, readUnary, *]

theorem readUnary_steps {A : Type} (xs : List A) (rest : List Bool) :
    (readUnary (unary xs ++ rest)).steps = 3*xs.length + 2 := by
  induction xs <;> simp [unary, readUnary, *]
  omega

theorem takeWord_value (xs rest : List Bool) :
    (takeWord (xs.map (fun _ => ())) (xs ++ rest)).value = some (xs, rest) := by
  induction xs <;> simp [takeWord, *]

theorem takeWord_steps (xs rest : List Bool) :
    (takeWord (xs.map (fun _ => ())) (xs ++ rest)).steps = 3*xs.length + 1 := by
  induction xs <;> simp [takeWord, *]
  omega

private def decodeLinks (tag : Bool) (rest : List Bool) : Run (Option (Node × List Bool)) :=
  let left := readUnary rest
  match left.value with
  | none => ⟨none, left.steps + 3⟩
  | some (a, rest) =>
    let right := readUnary rest
    ⟨right.value.map (fun p => (if tag then .cons a p.1 else .pair a p.1, p.2)),
      left.steps + right.steps + 4⟩

def decode : List Bool → Run (Option (Node × List Bool))
  | false :: false :: rest =>
    let len := readUnary rest
    match len.value with
    | none => ⟨none, len.steps + 3⟩
    | some (n, rest) =>
      let data := takeWord n rest
      ⟨data.value.map (fun p => (.word p.1, p.2)), len.steps + data.steps + 4⟩
  | tag :: true :: rest => decodeLinks tag rest
  | true :: false :: rest => ⟨some (.nil, rest), 3⟩
  | _ => ⟨none, 1⟩

private theorem units_map (xs : Address) : xs.map (fun _ => ()) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [ih]

theorem decode_value (n : Node) (rest : List Bool) :
    (decode (n.bits ++ rest)).value = some (n, rest) := by
  cases n <;>
    simp [decode, decodeLinks, Node.bits, List.append_assoc, readUnary_value,
      takeWord_value, units_map]

theorem decode_steps (n : Node) (rest : List Bool) :
    (decode (n.bits ++ rest)).steps ≤ 3*n.bits.length + 3 := by
  cases n <;>
    simp [decode, decodeLinks, Node.bits, List.append_assoc, readUnary_value,
      readUnary_steps, takeWord_steps, unary_length] <;> omega

end Signatures.Runtime.HeapBits
