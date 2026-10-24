import Proofs.Runtime.HeapPrimitive
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap FixedPorts WeierstrassCurve

namespace SignaturesTest.SharedHeap

private def address (n : Nat) : Address := List.replicate n ()

#eval show IO Unit from do
  let nodes : List Node := [.word [], .word [true, false, true], .nil,
    .pair [] (address 5), .cons (address 12) (address 3)]
  let rest := [true, true, false, true]
  for n in nodes do
    let encoded := encodeNode n
    unless encoded.value == n.bits do
      throw <| IO.userError "heap encoder changed node bits"
    unless encoded.steps ≤ 4*n.bits.length+3 do
      throw <| IO.userError "heap encoding exceeded cell bound"
    let decoded := decode (encoded.value ++ rest)
    unless decoded.value == some (n, rest) do
      throw <| IO.userError "heap decoder consumed a following node"
    unless decoded.steps ≤ 3*n.bits.length+3 do
      throw <| IO.userError "heap decoding exceeded cell bound"
  for bad in [[], [true], [false], [false, false, true, false], [false, true, true, true]] do
    unless (decode bad).value == none do
      throw <| IO.userError "truncated heap node was accepted"
  for i in List.range 8 do
    let r := read (address i) (tape nodes)
    unless r.value == nodes[i]? do
      throw <| IO.userError "node-indexed heap lookup mismatch"
    unless r.steps ≤ 3*(tape nodes).length + 7*(nodes.length+1) do
      throw <| IO.userError "heap lookup exceeded cell bound"

private def leaf (_ : Unit) (_ : List Bool) (_ : Unit) : Prop := False
private def typed : List Node := [.word (natBits 4 3), .pair [] [], .nil, .cons [] (address 2)]

private theorem number_rep : Represents 4 leaf typed .nat [] 3 :=
  .nat rfl (by decide)

example : Represents 4 leaf typed (.pair .nat .nat) (address 1) (3, 3) :=
  .pair rfl number_rep number_rep

example : Represents 4 leaf typed (.list .nat) (address 3) [3] :=
  .cons rfl number_rep (.nil rfl)

example : WellFormed 4 typed := by
  simp [typed, WellFormedFrom, NodeBound, natBits, address]

-- Truncation and forward/self references are not valid representation evidence.
example : ¬ Represents 4 leaf [.word (natBits 4 16)] .nat [] 16 := by
  intro h
  cases h with
  | nat _ hn => norm_num at hn

example : ¬ WellFormed 4 [.pair [] []] := by
  simp [WellFormedFrom, NodeBound]

example : ¬ Represents 4 leaf [.word [true, false]] .bool [] true := by
  intro h
  cases h with
  | bool hn => simp at hn

-- Each new pair points twice to the previous root. Its fully expanded value
-- would have 2^100 leaves, but only 101 nodes are allocated on the bit tape.
#eval show IO Unit from do
  let initial := alloc empty (.word [true])
  let mut root := initial.value.1
  let mut store := initial.value.2
  for _ in List.range 100 do
    let n := Node.pair root root
    let next := alloc store n
    unless next.steps ≤ 2*store.memory.length + 4*n.bits.length + 2*store.count.length + 8 do
      throw <| IO.userError "heap allocation exceeded cell bound"
    unless (read next.value.1 next.value.2.memory).value == some n do
      throw <| IO.userError "fresh shared node was not readable"
    store := next.value.2
    root := next.value.1
  unless store.count.length == 101 do
    throw <| IO.userError "sharing duplicated child nodes"
  unless store.memory.length ≤ 101*(2+2*101+4) do
    throw <| IO.userError "shared tape grew beyond its quadratic bound"
  unless (read [] store.memory).value == some (.word [true]) do
    throw <| IO.userError "allocation changed an old root"

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩

-- Runtime operands enter through allocated heap words, not constant circuits.
#eval show IO Unit from do
  let op := CryptoOp.add
  let code := CryptoCircuit.precompile 4 3 curve curve op
  for x in [0, 1, 2] do
    for y in [0, 1, 2] do
      let left := alloc empty (.word (natBits 4 x))
      let right := alloc left.value.2 (.word (natBits 4 y))
      let pair := alloc right.value.2 (.pair left.value.1 right.value.1)
      let store := pair.value.2
      let out := runPrimitive (inputLayout op) code store pair.value.1
      let some (root, next) := out.value | throw <| IO.userError "valid operand load failed"
      unless (read root next.memory).value == some (.word (natBits 4 ((x+y)%3))) do
        throw <| IO.userError "heap-backed primitive result mismatch"
      unless (read left.value.1 next.memory).value == some (.word (natBits 4 x)) do
        throw <| IO.userError "primitive allocation changed its operand"
      let m := (inputLayout op).width 4
      let n := 1+m+CryptoCircuit.gates 4 op
      let k := CryptoCircuit.outputWidth 4 op
      let size := store.memory.length
      let bound := 3*(3*size+7*(3+1)+2*m+5) + (n*(4*n+m+10)+k*(n+4)+3) +
        2*size+4*(3+2*k)+2*3+10
      unless out.steps ≤ bound do
        throw <| IO.userError "heap-backed primitive exceeded total cost"
  unless (runPrimitive (inputLayout op) code empty []).value.isNone do
    throw <| IO.userError "missing operand node was accepted"

end SignaturesTest.SharedHeap

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``encodeNode_value, ``encodeNode_steps, ``decode_value, ``decode_steps,
      ``read_value, ``read_steps, ``alloc_represents, ``alloc_steps, ``read_allocated,
      ``read_preserved, ``tape_length, ``Represents.append, ``alloc_pair, ``alloc_cons,
      ``pair_wellFormed, ``cons_wellFormed, ``Layout.encode_bits, ``loadPorts_value,
      ``loadPorts_steps, ``represents_range, ``runPrimitive_value,
      ``primitive_result_represents, ``runPrimitive_steps, ``primitive_wellFormed] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
