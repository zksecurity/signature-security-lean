import Proofs.Runtime.HeapDLog

open Signatures.Runtime

namespace SignaturesTest.HeapCodeSize

example (n : Nat) :
    (HeapExpression.Code.word (List.replicate n false)).cells = 2*n+2 := by
  simp [HeapExpression.Code.cells]

example (n : Nat) :
    (CircuitExecution.Instr.input (List.replicate n ())).cells = n+1 := by
  simp [CircuitExecution.Instr.cells]

example (n : Nat) :
    (BitRejection.Code.mk [] none (List.replicate n ())).cells = n+4 := by
  simp [BitRejection.Code.cells, Nat.add_assoc]

example (n : Nat) : CodeSize.natural n = 2*n.size+1 := rfl

example {a : Ty CryptoAtom} (layout : FixedPorts.Layout a)
    (code : CircuitExecution.Code) (arg : HeapExpression.Code) :
    (HeapExpression.Code.primitive layout code arg).cells =
      CodeSize.ty a+code.cells+arg.cells+1 := rfl

private def deadBranch (n : Nat) : HeapExpression.Code :=
  .branch (.word [true]) .nil (.word (List.replicate n false))

example (n : Nat) : 2*n ≤ (deadBranch n).cells := by
  simp only [deadBranch, HeapExpression.Code.cells, List.length_cons, List.length_nil,
    List.length_replicate]
  omega

-- Enlarging an unexecuted literal leaves online work unchanged but costs space.
#eval show IO Unit from do
  let small := deadBranch 0
  let large := deadBranch 2000
  unless (small.run [] SharedHeap.empty).steps == (large.run [] SharedHeap.empty).steps do
    throw <| IO.userError "unexecuted branch changed the online cost"
  unless large.cells == small.cells+4000 do
    throw <| IO.userError "unexecuted literal escaped the code-size budget"

-- Both program branches and fixed data are charged independently of execution.
example (c : HeapExpression.Code) (yes no : HeapProgram.Code (HeapMachine.Instruction .unit)) :
    no.cells HeapMachine.Instruction.cells ≤
      (HeapProgram.Code.branch c yes no).cells HeapMachine.Instruction.cells := by
  simp only [HeapProgram.Code.cells]
  omega

example (code : HeapMachine.Code) (value : HeapExpression.Code) :
    code.cells+value.cells < (HeapMachine.Package.mk [value] code).cells := by
  simp only [HeapMachine.Package.cells, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

-- The resource predicate must reject oversized packages even with unlimited time.
example {p w : Nat} [Fact p.Prime] {W : WeierstrassCurve.Affine (ZMod p)}
    (H : AddSubgroup W.Point)
    (pack : HeapMachine.Package) (codeBudget budget : Nat) (h : codeBudget < pack.cells) :
    ¬HeapMachine.dlogWithin w H codeBudget budget pack := by
  exact fun within => Nat.not_le_of_lt h within.1

-- The smaller DLog interface uses exactly the existing typed challenge encoding.
example {r p₁ p₂ w : Nat} [Fact p₁.Prime] [Fact p₂.Prime]
    {W₁ : WeierstrassCurve.Affine (ZMod p₁)} {W₂ : WeierstrassCurve.Affine (ZMod p₂)}
    {K M : Type} (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
    (encodeK : K → BitVec w) (encodeM : M → BitVec w) (pk : H₁) :
    HeapData.encodeEnv (r := r) (Γ := [point₁]) H₁ H₂ encodeK encodeM (pk, ()) =
      [.word (CryptoCircuit.pointBits (w := w) (pk : W₁.Point))] := rfl

end SignaturesTest.HeapCodeSize
