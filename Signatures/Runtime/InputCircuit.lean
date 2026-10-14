import Signatures.Runtime.CircuitWires

/-! Static input ports. The graph depends only on the public labels, never on
their runtime Boolean assignment. Each port adds exactly one input node. -/

namespace Signatures.Runtime.InputCircuit

open Std.Sat

variable {A : Type} [Hashable A] [DecidableEq A]

def build : {n : Nat} → (Fin n → A) → (aig : AIG A) → PrimeFieldCircuit.Built aig n
  | 0, _, aig => ⟨⟨aig, .empty⟩, .rfl⟩
  | n + 1, labels, aig =>
    let prev := build (fun i : Fin n => labels i.castSucc) aig
    let last := AIG.mkAtom prev.result.aig (labels (Fin.last n))
    let h := AIG.LawfulOperator.isPrefix_aig (f := AIG.mkAtom)
      prev.result.aig (labels (Fin.last n))
    ⟨⟨last.aig, (prev.result.vec.cast h.size_le).push last.ref⟩,
      CircuitWires.prefix_trans prev.extension h⟩

theorem build_size {n : Nat} (labels : Fin n → A) (aig : AIG A) :
    (build labels aig).result.aig.decls.size = aig.decls.size + n := by
  induction n with
  | zero => simp [build]
  | succ n ih => simp [build, AIG.mkAtom, ih, Nat.add_assoc]

theorem build_correct {n : Nat} (labels : Fin n → A) (aig : AIG A)
    (assign : A → Bool) (i : Fin n) :
    AIG.denote assign ⟨(build labels aig).result.aig,
      (build labels aig).result.vec.get i i.isLt⟩ = assign (labels i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [build, Fin.val_last, AIG.RefVec.get_push_ref_eq]
      exact AIG.denote_mkAtom
    · simp only [build, Fin.val_castSucc, AIG.RefVec.get_push_ref_lt _ _ _ j.isLt,
        AIG.RefVec.get_cast]
      exact (AIG.denote.eq_of_isPrefix _ _
        (AIG.LawfulOperator.isPrefix_aig (f := AIG.mkAtom) _ _)).trans
        (ih (fun k => labels k.castSucc) j)

/-- A pure wiring vector, with no allocation or graph extension. -/
def wires {aig : AIG A} : {n : Nat} → (Fin n → AIG.Ref aig) → AIG.RefVec aig n
  | 0, _ => .empty
  | n + 1, refs => (wires (fun i : Fin n => refs i.castSucc)).push (refs (Fin.last n))

theorem wires_get {aig : AIG A} {n : Nat} (refs : Fin n → AIG.Ref aig) (i : Fin n) :
    (wires refs).get i i.isLt = refs i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [wires]
    · simpa only [wires, Fin.val_castSucc, AIG.RefVec.get_push_ref_lt _ _ _ j.isLt]
        using ih (fun k => refs k.castSucc) j

end Signatures.Runtime.InputCircuit
