import Signatures.Runtime.AttachTable
import Signatures.Runtime.Table
import Signatures.Runtime.WeightedSum
import Signatures.Runtime.LookupExpr
import Mathlib.Algebra.BigOperators.Fin

/-! Canonical enumeration is fixed data, not an executable key-to-index instruction.
These equalities identify the results of charged table construction and summation with
the native finite-function representation used by the security reductions. -/

namespace Signatures.Runtime.AGM

noncomputable def canonicalKeys {ι I : Type} [Fintype ι] (encode : ι → I) : List I :=
  List.ofFn fun j => encode ((Fintype.equivFin ι).symm j)

theorem canonicalKeys_length {ι I : Type} [Fintype ι] (encode : ι → I) :
    (canonicalKeys encode).length = Fintype.card ι := by
  simp [canonicalKeys]

theorem canonicalKeys_attach {ι I V : Type} [Fintype ι]
    (encode : ι → I) (default : V) (values : List V) :
    (canonicalKeys encode).mapIdx (fun n i => (i, (values[n]?).getD default)) =
      canonicalKeys (fun i => (encode i, tableFunction default values i)) := by
  apply List.ext_getElem
  · simp [canonicalKeys]
  · intro n h₁ h₂
    simp [canonicalKeys, tableFunction]

theorem canonicalKeys_sum {ι I V : Type} [Fintype ι] [AddCommMonoid V]
    (encode : ι → I) (f : I → V) :
    ((canonicalKeys encode).map f).sum = ∑ i, f (encode i) := by
  simp only [canonicalKeys, List.map_ofFn, List.sum_ofFn]
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => f (encode i))

theorem lookupValue_map {ι I V : Type} [DecidableEq I]
    (encode : ι → I) (hinj : Function.Injective encode) (values : ι → V)
    (default : V) (keys : List ι) (i : ι) (hi : i ∈ keys) :
    lookupValue (encode i) default (keys.map fun j => (encode j, values j)) = (true, values i) := by
  classical
  induction keys with
  | nil => simp at hi
  | cons j keys ih =>
      by_cases h : j = i
      · subst j
        simp [lookupValue]
      · have he : encode j ≠ encode i := fun he => h (hinj he)
        simp only [List.map_cons, lookupValue, he, ite_false]
        exact ih (by simpa [Ne.symm h] using hi)

theorem lookupValue_canonical {ι I V : Type} [Fintype ι] [DecidableEq I]
    (encode : ι → I) (hinj : Function.Injective encode) (values : ι → V)
    (default : V) (i : ι) :
    lookupValue (encode i) default (canonicalKeys fun j => (encode j, values j)) =
      (true, values i) := by
  have hi : i ∈ canonicalKeys (id : ι → ι) := by
    simp only [canonicalKeys, List.mem_ofFn]
    exact ⟨Fintype.equivFin ι i, by simp⟩
  simpa only [canonicalKeys, List.map_ofFn, id_eq, Function.comp_def] using
    lookupValue_map encode hinj values default (canonicalKeys (id : ι → ι)) i hi

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {indexTy messageTy : Ty CryptoAtom}

theorem attachTable_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (default : F) (values : List F) :
    ((attachTable (indexTy := indexTy)).run (arithmetic F G₁ G₂ K M cost)
      (default, canonicalKeys encode, values, ())).value =
      canonicalKeys (fun i => (encode i, tableFunction default values i)) := by
  rw [attachTable_value, canonicalKeys_attach]

theorem weightedSum_native {ι : Type} [Fintype ι]
    (cost : PrimitiveCosts) (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (default : F) (values : List F)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    ((weightedSum weight).run (arithmetic F G₁ G₂ K M cost)
      (m, (attachTable.run (arithmetic F G₁ G₂ K M cost)
        (default, canonicalKeys encode, values, ())).value, ())).value =
      ∑ i, tableFunction default values i *
        (weight.run (arithmetic F G₁ G₂ K M cost) (encode i, m, ())).value := by
  rw [attachTable_native, weightedSum_value, canonicalKeys_sum]

theorem lookupExpr_native {ι : Type} [Fintype ι]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts) (encode : ι → indexTy.Value (cryptoBase F G₁ G₂ K M))
    (hinj : Function.Injective encode) (default : F) (values : List F)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (i : ι) :
    ((lookupExpr eq).run (arithmetic F G₁ G₂ K M cost)
      (encode i, default, (attachTable.run (arithmetic F G₁ G₂ K M cost)
        (default, canonicalKeys encode, values, ())).value, ())).value =
      (true, tableFunction default values i) := by
  rw [attachTable_native, lookupExpr_value _ _ heq]
  exact lookupValue_canonical encode hinj (tableFunction default values) default i

end Signatures.Runtime.AGM
