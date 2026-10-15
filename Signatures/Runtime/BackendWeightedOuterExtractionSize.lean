import Signatures.Runtime.BackendWeightedExtractionArgs

/-! The complete outer extractor retains both reply logs and the full attacker
output through every phase. These size bounds count that entire environment. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

variable {indexTy messageTy : Ty CryptoAtom}

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem extraction_target_size
    (output : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) (width : Nat)
    (hi : Q.size (rep.env [AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) (output, tr, ()) ≤ width) :
    Q.size (rep.ty messageTy) output.1 ≤ width := by
  exact (sizes.fst_le (rep.ty messageTy)
    (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) output).trans
      ((sizes.fst_le (rep.ty (AGM.outputTy messageTy)) (rep.env [(Reply.transcriptTy indexTy messageTy)]) (output, tr, ())).trans hi)

theorem extractionFrames_size {value : Ty CryptoAtom}
    (env : Env (cryptoBase F G₁ G₂ K M) [AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width)
    (hd : Q.size (rep.ty (evalRowTy indexTy)) default ≤ width)
    (hv : ∀ x : value.Value (cryptoBase F G₁ G₂ K M), Q.size (rep.ty value) x ≤ width) :
    Q.size (rep.env [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) (default, env) ≤ 3 * width ∧
    (∀ x, Q.size (rep.env [value, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) (x, default, env) ≤ 5 * width) ∧
    (∀ x y, Q.size (rep.env [value, value, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
      (x, y, default, env) ≤ 7 * width) ∧
    (∀ x y z, Q.size (rep.env [value, value, value, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
      (x, y, z, default, env) ≤ 9 * width) := by
  have hp := @sizes.prod_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [LanguageRepresentation.env] at *
    grind only
  · intro x
    dsimp only [LanguageRepresentation.env] at *
    grind only
  · intro x y
    dsimp only [LanguageRepresentation.env] at *
    grind only
  · intro x y z
    dsimp only [LanguageRepresentation.env] at *
    grind only

theorem extractionInputs_size
    (output : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) (width : Nat)
    (hi : Q.size (rep.env [AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) (output, tr, ()) ≤ width) :
    Q.size (rep.ty (.list (AGM.tokenTy indexTy))) tr.1 ≤ width ∧
      Q.size (rep.ty (.list (AGM.tokenTy messageTy))) tr.2 ≤ width ∧
      Q.size (rep.ty (.list scalar)) output.2.2.1 ≤ width ∧
      Q.size (rep.ty (.list scalar)) output.2.2.2 ≤ width := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem extractionArgumentFrame_size
    (tokens : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (ht : Q.size (rep.ty (.list (AGM.tokenTy messageTy))) tokens ≤ width)
    (hc : Q.size (rep.ty (.list scalar)) coeff ≤ width)
    (hd : Q.size (rep.ty (evalRowTy indexTy)) default ≤ width) :
    Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar, (evalRowTy indexTy)])
      (tokens, coeff, default, ()) ≤ 7 * width := by
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

theorem extractionTargetFrame_size
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty messageTy) m ≤ width) (hd : Q.size (rep.ty (evalRowTy indexTy)) default ≤ width) :
    Q.size (rep.env [messageTy, evalRowTy indexTy]) (m, default, ()) ≤ 5 * width := by
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.WeightedAGM.Extract
