import Proofs.Runtime.BackendWeightedHashExtraction
import Proofs.Runtime.BackendWeightedSigningExtraction
import Proofs.Runtime.BackendWeightedTargetExtraction
import Proofs.Runtime.BackendWeightedExtractionArgs
import Proofs.Runtime.BackendWeightedOuterExtractionSize

/-! One explicit width covering all phases of weighted extraction. The bound
uses transcript lengths, coefficient lengths, and encountered encodings; it
contains no cardinality of the message or index domain. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate LazyAGM.ReplySyntax

def extractionWidth (index : Index) (width hashCap signCap coeffCap cacheCap : Nat) : Nat :=
  32 * width + preparationFrameWidth width (hashCap + signCap) coeffCap
    (hashCap + signCap * (index.bound + 1) + (index.bound + 1)) (cacheCap + (index.bound + 1)) +
    hashEvaluationWidth width hashCap cacheCap +
    goodCoefficientEvaluationWidth index width signCap cacheCap +
    badCoefficientEvaluationWidth index width signCap cacheCap +
    Reply.goodSignEvaluationWidth index width cacheCap +
    Reply.badSignEvaluationWidth index width cacheCap

theorem extractionWidth_bounds (index : Index) (width hashCap signCap coeffCap cacheCap : Nat) :
    32 * width ≤ extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    preparationFrameWidth width (hashCap + signCap) coeffCap
      (hashCap + signCap * (index.bound + 1) + (index.bound + 1)) (cacheCap + (index.bound + 1)) ≤
      extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    hashEvaluationWidth width hashCap cacheCap ≤ extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    goodCoefficientEvaluationWidth index width signCap cacheCap ≤ extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    badCoefficientEvaluationWidth index width signCap cacheCap ≤ extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    Reply.goodSignEvaluationWidth index width cacheCap ≤ extractionWidth index width hashCap signCap coeffCap cacheCap ∧
    Reply.badSignEvaluationWidth index width cacheCap ≤ extractionWidth index width hashCap signCap coeffCap cacheCap := by
  unfold extractionWidth
  omega

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (cost : PrimitiveCosts) {header : Nat} (sizes : SizeLaws Q header)
  (lists : ListSizeLaws Q rep.data header)

omit rep sizes lists in
theorem defaultRow_denote (index : Index)
    (output : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    (defaultRow index.defaultTerm).denote (arithmetic F G₁ G₂ K M cost) (output, tr, ()) =
      index.defaultTerm.denote (arithmetic F G₁ G₂ K M cost) (output.1, ()) := by
  simpa only [defaultRow, Expr.denote, v0, Var.get, Env.append] using
    index.defaultTerm.weakenTail_denote
      (Δ := [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy])
      (arithmetic F G₁ G₂ K M cost)
      (output.1, ()) (output, tr, ())

include sizes in
theorem defaultRow_size (index : Index)
    (output : (AGM.outputTy index.messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy]) (output, tr, ()) ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hj : Q.size (rep.ty (boundedNat index.bound)) (0 : Fin (index.bound + 1)) ≤ width) :
    Q.size (rep.ty (evalRowTy index.ty))
      ((defaultRow index.defaultTerm).denote (arithmetic F G₁ G₂ K M cost) (output, tr, ())) ≤ 5 * width := by
  rw [defaultRow_denote]
  exact index.default_size rep cost sizes output.1 width hh
    (extraction_target_size rep sizes output tr width hi) hf hj

include sizes lists in
omit [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M] in
theorem extractionCache_size (index : Index) {value : Ty CryptoAtom}
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (width hashCap signCap coeffCap cacheCap : Nat)
    (hh : header ≤ width)
    (hk : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ 5 * width)
    (hv : ∀ x, Q.size (rep.ty value) x ≤ 3 * width)
    (hc : cache.length ≤ cacheCap) :
    Q.size (rep.ty (Read.cacheTy index.ty value)) cache ≤ extractionWidth index width hashCap signCap coeffCap cacheCap := by
  exact (preparationCache_size rep sizes lists (indexTy := index.ty) (value := value) cache
    width (hashCap + signCap) coeffCap (hashCap + signCap * (index.bound + 1) + (index.bound + 1))
    (cacheCap + (index.bound + 1)) hh (fun p hp => (hk p hp).trans (by omega)) hv (by omega)).trans
    (extractionWidth_bounds index width hashCap signCap coeffCap cacheCap).2.1

end Signatures.Runtime.WeightedAGM.Extract
