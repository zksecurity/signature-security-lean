import Signatures.Runtime.BackendWeightedReply

/-! Exact source equations for the four actual weighted reply programs. The
signing equations include executed term construction and complete private-cache
evaluation; one explicit reply is logged regardless of the term-list length. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM

namespace Signatures.Runtime.WeightedAGM

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

instance Index.messageValueDecidableEq (index : Index) :
    DecidableEq (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) := by
  cases index with
  | oops d => exact inferInstanceAs (DecidableEq (F × K))
  | proximity ell =>
    letI : DecidableEq ((tupleTy scalar ell).Value (cryptoBase F G₁ G₂ K M)) := by
      induction ell with
      | zero => exact inferInstanceAs (DecidableEq Unit)
      | succ ell ih => exact inferInstanceAs (DecidableEq (F × (tupleTy scalar ell).Value (cryptoBase F G₁ G₂ K M)))
    exact inferInstanceAs (DecidableEq ((tupleTy scalar ell).Value (cryptoBase F G₁ G₂ K M) × K))

def Index.sourceTerms (cost : PrimitiveCosts) (index : Index)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M)) :
    List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F) :=
  index.terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())

theorem Index.oops_sourceTerms (cost : PrimitiveCosts) (d : Nat) (m : F × K) :
    Index.sourceTerms (G₁ := G₁) (G₂ := G₂) (M := M) cost (.oops d) m = OOPS.LazyAGM.terms d m := by
  exact (Expr.run_value _ _ _).symm.trans (Terms.oops_value cost d m)

theorem Index.proximity_sourceTerms (cost : PrimitiveCosts) (ell : Nat)
    (m : (Weights.proximityTupleMessage ell).Value (cryptoBase F G₁ G₂ K M)) :
    Index.sourceTerms cost (.proximity ell) m =
      (Proximity.LazyAGM.terms (Weights.proximityMessageEquiv ell m)).map
        (Prod.map Weights.encodeProximityKey id) := by
  exact (Expr.run_value _ _ _).symm.trans (Terms.proximity_value cost ell m)

namespace Reply

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
  (g X : G₁)
  (tr : Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)

theorem goodHash_denote (i : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodHash rep data cost primitive sampling index).denote (i, (g, X), cache, tr) =
      (fun p => (p.1 • g, (g, X), p.2, record (.inl i) (p.1 • g) tr)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F)) (.inr i)).run cache := by
  rw [goodHash.eq_def, backendReply_denote, Read.goodRead_denote]
  rfl

theorem goodSign_denote (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodSign rep data cost primitive sampling index).denote (m, (g, X), cache, tr) =
      (fun p => (p.1 • X, (g, X), p.2, record (.inr m) (p.1 • X) tr)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F))
          (evalTerms (index.sourceTerms cost m))).run cache := by
  rw [goodSign.eq_def, backendReply_denote, goodSignValue_source]
  rfl

theorem badHash_denote (kappa : F) (i : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (badHash rep data cost primitive sampling index).denote (i, (kappa, g, X), cache, tr) =
      (fun p => let point := p.1.1 • X + p.1.2 • g
        (point, (kappa, g, X), p.2, record (.inl i) point tr)) <$>
        ((BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F)) (.inr i)).run cache := by
  rw [badHash.eq_def, backendReply_denote, Read.badRead_denote]
  rfl

theorem badSign_denote (kappa : F) (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (badSign rep data cost primitive sampling index).denote (m, (kappa, g, X), cache, tr) =
      (fun p => let point := kappa • (p.1.1 • X + p.1.2 • g)
        (point, (kappa, g, X), p.2, record (.inr m) point tr)) <$>
        (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
          (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F))
          (evalTerms (index.sourceTerms cost m))).run cache := by
  rw [badSign.eq_def, backendReply_denote, badSignValue_source]
  rfl

end Reply
end Signatures.Runtime.WeightedAGM
