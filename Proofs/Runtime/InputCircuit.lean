import Proofs.Runtime.CircuitWires

/-! Static input ports. The graph depends only on the public labels, never on
their runtime Boolean assignment. Each port adds exactly one input node. -/

namespace Signatures.Runtime.InputCircuit

open Std.Sat

variable {A : Type} [Hashable A] [DecidableEq A]

def build : {n : Nat} → (Fin n → A) → (aig : AIG A) → PrimeFieldCircuit.Built aig n
  | 0, _, aig => ⟨⟨aig, .empty⟩, .rfl⟩
  | n + 1, labels, aig =>
    let prev := build (fun i : Fin n => labels i.castSucc) aig
    let last := AIG.mkAtomCached prev.result.aig (labels (Fin.last n))
    let h := AIG.LawfulOperator.isPrefix_aig (f := AIG.mkAtomCached)
      prev.result.aig (labels (Fin.last n))
    ⟨⟨last.aig, (prev.result.vec.cast h.size_le).push last.ref⟩,
      CircuitWires.prefix_trans prev.extension h⟩

/-- `mkAtomCached` reuses an existing atom node, so a port only allocates when
its label is fresh: distinct labels, none already present in `aig`. -/
theorem build_decls {n : Nat} (labels : Fin n → A) (aig : AIG A)
    (hinj : Function.Injective labels)
    (hfresh : ∀ i, AIG.Decl.atom (labels i) ∉ aig.decls) :
    (build labels aig).result.aig.decls =
      aig.decls ++ Array.ofFn (fun i => AIG.Decl.atom (labels i)) := by
  induction n with
  | zero => simp [build]
  | succ n ih =>
    have hprev := ih (fun i : Fin n => labels i.castSucc)
      (fun _ _ h => Fin.castSucc_injective _ (hinj h)) (fun i => hfresh _)
    have hmiss : (build (fun i : Fin n => labels i.castSucc) aig).result.aig.cache.get?
        (.atom (labels (Fin.last n))) = none := by
      cases hc : (build (fun i : Fin n => labels i.castSucc) aig).result.aig.cache.get?
          (.atom (labels (Fin.last n))) with
      | none => rfl
      | some hit =>
        exfalso
        have hmem : AIG.Decl.atom (labels (Fin.last n)) ∈
            (build (fun i : Fin n => labels i.castSucc) aig).result.aig.decls :=
          hit.hvalid ▸ Array.getElem_mem hit.hbound
        rw [hprev, Array.mem_append, Array.mem_ofFn] at hmem
        rcases hmem with h | ⟨j, hj⟩
        · exact hfresh _ h
        · exact (Fin.castSucc_lt_last j).ne (hinj (AIG.Decl.atom.inj hj))
    simp only [build]
    rw [AIG.mkAtomCached_miss_aig _ hmiss, hprev, Array.ofFn_succ, Array.append_push]
    rfl

theorem build_size {n : Nat} (labels : Fin n → A) (aig : AIG A)
    (hinj : Function.Injective labels)
    (hfresh : ∀ i, AIG.Decl.atom (labels i) ∉ aig.decls) :
    (build labels aig).result.aig.decls.size = aig.decls.size + n := by
  simp [build_decls labels aig hinj hfresh]

theorem build_empty_size {n : Nat} {labels : Fin n → A} (hinj : Function.Injective labels) :
    (build labels (AIG.empty : AIG A)).result.aig.decls.size = 1 + n := by
  rw [build_size labels AIG.empty hinj
    (fun _ h => absurd (Array.mem_singleton.mp h) (by simp))]
  rfl

theorem build_correct {n : Nat} (labels : Fin n → A) (aig : AIG A)
    (assign : A → Bool) (i : Fin n) :
    AIG.denote assign ⟨(build labels aig).result.aig,
      (build labels aig).result.vec.get i i.isLt⟩ = assign (labels i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [build, Fin.val_last, AIG.RefVec.get_push_ref_eq]
      exact AIG.denote_mkAtomCached
    · simp only [build, Fin.val_castSucc, AIG.RefVec.get_push_ref_lt _ _ _ j.isLt,
        AIG.RefVec.get_cast]
      exact (AIG.denote.eq_of_isPrefix _ _
        (AIG.LawfulOperator.isPrefix_aig (f := AIG.mkAtomCached) _ _)).trans
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

