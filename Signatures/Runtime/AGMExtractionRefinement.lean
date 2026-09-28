import Signatures.Runtime.AGMSource

/-! Transport compiled extraction through the query/message representations. The scalar
result functions below are the existing native reductions' final pure expressions; they
are proof specifications, not added machine instructions. -/

namespace Signatures.Runtime.AGM

def goodResult {F I N G : Type} [Field F] [Fintype I] [DecidableEq I]
    (w : I → N → F) (rho : I → F) (out : Model.LazyAGM.Output F N)
    (tr : Model.LazyAGM.Transcript I N G) : F :=
  (out.β + ∑ i, Model.LazyAGM.baseCoeff out.γ tr.1 i * rho i) /
    ((∑ i, rho i * w i out.mstar) -
      (tr.2.mapIdx fun n p => Model.LazyAGM.tokenCoeff out.ξ n * (∑ i, rho i * w i p.1)).sum)

def badResult {F I N G : Type} [Field F] [Fintype I]
    (w : I → N → F) (a b : I → F) (out : Model.LazyAGM.Output F N)
    (tr : Model.LazyAGM.Transcript I N G) : F :=
  -(∑ i, Model.LazyAGM.denominatorCoeff w out tr i * b i) /
    (∑ i, Model.LazyAGM.denominatorCoeff w out tr i * a i)

theorem baseCoeff_decode {F I J G : Type} [AddCommMonoid F] [DecidableEq I] [DecidableEq J]
    (index : J ≃ I) (coeff : List F) (tr : List (J × G)) (i : I) :
    Model.LazyAGM.baseCoeff coeff tr (index.symm i) =
      Model.LazyAGM.baseCoeff coeff (tr.map fun p => (index p.1, p.2)) i := by
  simp [Model.LazyAGM.baseCoeff, List.mapIdx_eq_ofFn, List.sum_ofFn, Equiv.eq_symm_apply]

variable {F G₁ G₂ K M I N : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {indexTy messageTy : Ty CryptoAtom}

omit [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem denominatorCoeff_decode
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N)
    (w : I → N → F) (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) (i : I) :
    Model.LazyAGM.denominatorCoeff (fun j m => w (index j) (message m)) (outputView out)
      (tr.1.reverse, tr.2.reverse) (index.symm i) =
      Model.LazyAGM.denominatorCoeff w (decodeOutput message out) (transcriptView index message tr) i := by
  simp [Model.LazyAGM.denominatorCoeff, outputView, decodeOutput, transcriptView,
    List.mapIdx_eq_ofFn, List.sum_ofFn]

theorem goodExtract_native [Fintype I] [DecidableEq I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cost : PrimitiveCosts)
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (rho : I → F) (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((goodExtract eq weight).run (arithmetic F G₁ G₂ K M cost)
      (out, tr, canonicalKeys (fun i => (index.symm i, rho i)), ())).value =
      goodResult w rho (decodeOutput message out) (transcriptView index message tr) := by
  rw [goodExtract_value]
  have h := goodCore_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost eq heq weight index.symm rho (outputView out) (tr.1.reverse, tr.2.reverse)
  refine h.trans ?_
  simp only [hw, Equiv.apply_symm_apply]
  simp [goodResult, outputView, decodeOutput, transcriptView, baseCoeff_decode,
    List.mapIdx_eq_ofFn, List.sum_ofFn]

theorem badExtract_native [Fintype I]
    (cost : PrimitiveCosts)
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (a b : I → F) (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    ((badExtract weight).run (arithmetic F G₁ G₂ K M cost)
      (out, tr, canonicalKeys (fun i => (index.symm i, a i)),
        canonicalKeys (fun i => (index.symm i, b i)), ())).value =
      badResult w a b (decodeOutput message out) (transcriptView index message tr) := by
  rw [badExtract_value]
  have h := badCore_native (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost weight index.symm a b (outputView out) (tr.1.reverse, tr.2.reverse)
  refine h.trans ?_
  simp only [hw, denominatorCoeff_decode (G₁ := G₁) (G₂ := G₂) (K := K) (M := M), badResult]

end Signatures.Runtime.AGM
