import Proofs.Runtime.FieldProgram

/-! Multiple field outputs on one shared circuit. Earlier output wires remain
valid while later outputs are compiled. -/

namespace Signatures.Runtime.FieldProgram

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open PrimeFieldCircuit (Built Represents)

variable {A : Type} [Hashable A] [DecidableEq A] {w : Nat}

structure Bundle (aig : AIG A) (w k : Nat) where
  graph : AIG A
  refs : Fin k → AIG.RefVec graph w
  extension : AIG.IsPrefix aig.decls graph.decls

def Bundle.cast {aig : AIG A} {k v : Nat} (out : Bundle aig w k) (ref : AIG.RefVec aig v) :
    AIG.RefVec out.graph v := ref.cast out.extension.size_le

def Bundle.castRef {aig : AIG A} {k : Nat} (out : Bundle aig w k) (ref : AIG.Ref aig) :
    AIG.Ref out.graph := ref.cast out.extension.size_le

theorem Bundle.preservesRef {aig : AIG A} {k : Nat} (out : Bundle aig w k) (assign : A → Bool)
    (ref : AIG.Ref aig) : AIG.denote assign ⟨out.graph, out.castRef ref⟩ = AIG.denote assign ⟨aig, ref⟩ :=
  AIG.denote.eq_of_isPrefix ⟨aig, ref⟩ _ out.extension

def Bundle.chain {aig : AIG A} {j k : Nat} (out : Bundle aig w j) (next : Bundle out.graph w k) :
    Bundle aig w k :=
  ⟨next.graph, next.refs, ⟨out.extension.size_le.trans next.extension.size_le,
    fun i hi => (next.extension.idx_eq i (hi.trans_le out.extension.size_le)).trans (out.extension.idx_eq i hi)⟩⟩

theorem Bundle.chain_correct {aig : AIG A} {j k : Nat} (out : Bundle aig w j)
    (next : Bundle out.graph w k) (assign : A → Bool) (values : Fin k → BitVec w)
    (h : ∀ i, Represents assign next.graph (next.refs i) (values i)) :
    ∀ i, Represents assign (out.chain next).graph ((out.chain next).refs i) (values i) := h

theorem Bundle.chain_size {aig : AIG A} {j k : Nat} (out : Bundle aig w j)
    (next : Bundle out.graph w k) : (out.chain next).graph.decls.size = next.graph.decls.size := rfl

theorem Bundle.preserves {aig : AIG A} {k v : Nat} (out : Bundle aig w k) (assign : A → Bool)
    (ref : AIG.RefVec aig v) (value : BitVec v) (h : Represents assign aig ref value) :
    Represents assign out.graph (out.cast ref) value := by
  intro i hi
  rw [Bundle.cast, AIG.RefVec.get_cast]
  exact (AIG.denote.eq_of_isPrefix ⟨aig, ref.get i hi⟩ _ out.extension).trans (h i hi)

def compileMany (p : Nat) {n : Nat} : {k : Nat} → (Fin k → Code n) →
    (aig : AIG A) → (Fin n → AIG.RefVec aig w) → Bundle aig w k
  | 0, _, aig, _ => ⟨aig, Fin.elim0, AIG.IsPrefix.rfl⟩
  | k + 1, code, aig, env =>
    let head := (code 0).compile p aig env
    let tail := compileMany p (fun i : Fin k => code i.succ) head.result.aig (fun i => head.cast (env i))
    ⟨tail.graph, Fin.cases (tail.cast head.result.vec) tail.refs,
      ⟨head.extension.size_le.trans tail.extension.size_le, fun i hi =>
        (tail.extension.idx_eq i (hi.trans_le head.extension.size_le)).trans (head.extension.idx_eq i hi)⟩⟩

theorem compileMany_size {p : Nat} [Fact p.Prime] (hfit : p * p ≤ 2 ^ w)
    {n k : Nat} (code : Fin k → Code n) (aig : AIG A) (env : Fin n → AIG.RefVec aig w) :
    (compileMany p code aig env).graph.decls.size ≤ aig.decls.size + ∑ i, (code i).gates w := by
  induction k generalizing aig with
  | zero => simp [compileMany]
  | succ k ih =>
    dsimp only [compileMany]
    refine (ih _ _ _).trans ?_
    rw [Fin.sum_univ_succ]
    have := (code 0).compile_size hfit aig env
    omega

theorem compileMany_correct {p : Nat} [Fact p.Prime] (hfit : p * p ≤ 2 ^ w) (hp : 2 < p)
    {n k : Nat} (code : Fin k → Code n) (aig : AIG A) (env : Fin n → AIG.RefVec aig w)
    (assign : A → Bool) (values : Fin n → ZMod p)
    (h : ∀ i, Represents assign aig (env i) (BitVec.ofNat w (values i).val)) (j : Fin k) :
    Represents assign (compileMany p code aig env).graph (compileMany p code aig env |>.refs j)
      (BitVec.ofNat w ((code j).eval values).val) := by
  induction k generalizing aig with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    let head := (code 0).compile p aig env
    let tail := compileMany p (fun i : Fin k => code i.succ) head.result.aig (fun i => head.cast (env i))
    refine Fin.cases ?_ (fun i => ?_) j
    · exact tail.preserves assign head.result.vec _ ((code 0).compile_correct hfit hp aig env assign values h)
    · exact ih (fun i => code i.succ) head.result.aig _
        (fun i => head.preserves assign (env i) _ (h i)) i

end Signatures.Runtime.FieldProgram
