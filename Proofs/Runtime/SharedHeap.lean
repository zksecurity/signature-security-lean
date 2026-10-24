import Proofs.Runtime.HeapBits

/-! An append-only shared heap with a concrete bit-tape representation. Unary
addresses index nodes. Reads decode the tape and allocations copy its bit cells;
neither operation assumes constant-time access to arbitrary-sized values. -/

namespace Signatures.Runtime.SharedHeap

open HeapBits

def tape (heap : List Node) : List Bool := heap.flatMap Node.bits

def read : Address → List Bool → Run (Option Node)
  | [], input =>
    let node := decode input
    ⟨node.value.map Prod.fst, node.steps + 1⟩
  | _ :: addr, input =>
    let node := decode input
    match node.value with
    | none => ⟨none, node.steps + 1⟩
    | some (_, rest) =>
      let next := read addr rest
      ⟨next.value, node.steps + next.steps + 2⟩

theorem read_value (heap : List Node) (addr : Address) :
    (read addr (tape heap)).value = heap[addr.length]? := by
  induction heap generalizing addr with
  | nil => cases addr <;> simp [tape, read, decode]
  | cons n heap ih =>
    cases addr <;> simp [tape, read, decode_value]
    exact ih _

theorem read_steps (heap : List Node) (addr : Address) :
    (read addr (tape heap)).steps ≤ 3*(tape heap).length + 7*(heap.length + 1) := by
  induction heap generalizing addr with
  | nil => cases addr <;> simp [tape, read, decode]
  | cons n heap ih =>
    have hn := decode_steps n (tape heap)
    cases addr with
    | nil =>
      simp only [tape, List.flatMap_cons, read, decode_value]
      simp only [tape, List.length_append, List.length_cons] at *
      omega
    | cons u addr =>
      have ht := ih addr
      simp only [tape, List.flatMap_cons, read, decode_value]
      simp only [tape, List.length_append, List.length_cons] at *
      omega

structure Store where
  count : Address
  memory : List Bool
  deriving Repr

def Store.Represents (store : Store) (heap : List Node) : Prop :=
  store.count.length = heap.length ∧ store.memory = tape heap

def empty : Store := ⟨[], []⟩

theorem empty_represents : empty.Represents [] := ⟨rfl, rfl⟩

/-- Append one node, preserving its child references. The returned address is
copied from the node counter; no child value is traversed or duplicated. -/
def alloc (store : Store) (node : Node) : Run (Address × Store) :=
  let bits := encodeNode node
  let memory := HeapBits.append store.memory bits.value
  let addr := HeapBits.copy store.count
  ⟨(addr.value, ⟨() :: store.count, memory.value⟩), bits.steps + memory.steps + addr.steps + 3⟩

theorem alloc_address (store : Store) (node : Node) :
    (alloc store node).value.1 = store.count := copy_value _

theorem alloc_represents (store : Store) (heap : List Node) (hs : store.Represents heap)
    (node : Node) : (alloc store node).value.2.Represents (heap ++ [node]) := by
  rcases hs with ⟨hc, hm⟩
  simp [alloc, Store.Represents, append_value, encodeNode_value, hc, hm, tape,
    List.flatMap_append, Nat.add_comm]

theorem alloc_steps (store : Store) (node : Node) :
    (alloc store node).steps ≤ 2*store.memory.length + 4*node.bits.length + 2*store.count.length + 8 := by
  have h := encodeNode_steps node
  simp only [alloc, append_steps, copy_steps]
  omega

theorem read_allocated (store : Store) (heap : List Node) (hs : store.Represents heap)
    (node : Node) :
    (read (alloc store node).value.1 (alloc store node).value.2.memory).value = some node := by
  rw [(alloc_represents store heap hs node).2, read_value, alloc_address, hs.1]
  simp

theorem read_preserved (store : Store) (heap : List Node) (hs : store.Represents heap)
    (node : Node) (addr : Address) (ha : addr.length < heap.length) :
    (read addr (alloc store node).value.2.memory).value = (read addr store.memory).value := by
  rw [(alloc_represents store heap hs node).2, hs.2, read_value, read_value]
  exact List.getElem?_append_left ha

/-- Every child points backwards, and leaf payloads have a common bit cap. -/
def NodeBound (wordBits nodes : Nat) : Node → Prop
  | .word xs => xs.length ≤ wordBits
  | .pair a b | .cons a b => a.length < nodes ∧ b.length < nodes
  | .nil => True

theorem nodeBound_mono {w n k : Nat} (h : n ≤ k) (node : Node)
    (hn : NodeBound w n node) : NodeBound w k node := by
  cases node <;> simp only [NodeBound] at * <;> omega

theorem node_bits_length {w n : Nat} (node : Node) (hn : NodeBound w n node) :
    node.bits.length ≤ 2*w + 2*n + 4 := by
  cases node <;> simp [NodeBound, Node.bits, unary_length] at * <;> omega

def WellFormedFrom (wordBits : Nat) : Nat → List Node → Prop
  | _, [] => True
  | start, node :: rest => NodeBound wordBits start node ∧ WellFormedFrom wordBits (start+1) rest

abbrev WellFormed (wordBits : Nat) (heap : List Node) : Prop := WellFormedFrom wordBits 0 heap

theorem wellFormedFrom_lookup {w start i : Nat} {heap : List Node} {node : Node}
    (hh : WellFormedFrom w start heap) (hn : heap[i]? = some node) : NodeBound w (start+i) node := by
  induction heap generalizing start i with
  | nil => simp at hn
  | cons head rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst node
      simpa using hh.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at hn
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hh.2 hn

theorem wellFormed_lookup {w i : Nat} {heap : List Node} {node : Node}
    (hh : WellFormed w heap) (hn : heap[i]? = some node) : NodeBound w i node := by
  simpa only [Nat.zero_add] using wellFormedFrom_lookup hh hn

theorem wellFormed_append {w start : Nat} (heap : List Node) (node : Node)
    (hh : WellFormedFrom w start heap) (hn : NodeBound w (start + heap.length) node) :
    WellFormedFrom w start (heap ++ [node]) := by
  induction heap generalizing start with
  | nil => exact ⟨hn, trivial⟩
  | cons head rest ih =>
    exact ⟨hh.1, ih hh.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn)⟩

theorem wellFormed_nodes {w start : Nat} (heap : List Node)
    (hh : WellFormedFrom w start heap) : ∀ node ∈ heap, NodeBound w (start + heap.length) node := by
  induction heap generalizing start with
  | nil => simp
  | cons head rest ih =>
    intro node hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact nodeBound_mono (n := start) (by simp) node hh.1
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hh.2 node hn

private theorem tape_length_of_bounded (heap : List Node) (w n : Nat)
    (hh : ∀ node ∈ heap, NodeBound w n node) :
    (tape heap).length ≤ heap.length * (2*w + 2*n + 4) := by
  induction heap with
  | nil => simp [tape]
  | cons node rest ih =>
    have hn := node_bits_length node (hh node (by simp))
    have ht := ih (fun node h => hh node (by simp [h]))
    simp only [tape, List.flatMap_cons, List.length_append, List.length_cons] at *
    nlinarith

/-- Shared values occupy polynomial space in allocated nodes and word width,
regardless of how large their recursively unfolded mathematical values are. -/
theorem tape_length {w : Nat} (heap : List Node) (hh : WellFormed w heap) :
    (tape heap).length ≤ heap.length * (2*w + 2*heap.length + 4) := by
  apply tape_length_of_bounded
  simpa only [Nat.zero_add] using wellFormed_nodes heap hh

end Signatures.Runtime.SharedHeap
