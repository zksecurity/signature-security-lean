import Signatures.Runtime.BackendLazyAGMTokensSize
import Signatures.Runtime.BackendLazyAGMExtraction

/-! Whole-extractor encoding bounds, including all attacker output and both
transcripts in retained caller frames. Cache invariants refer only to stored
entries and their key sizes, never to a finite message universe. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def ExtractionCache {M R : Type} (valid : M → Prop) (cap : Nat) (cache : List (M × R)) : Prop :=
  cache.length ≤ cap ∧ ∀ entry ∈ cache, valid entry.1

def extractionWidth (width queryCap coeffCap cacheCap : Nat) : Nat :=
  tokenFrameWidth (5 * width) queryCap coeffCap (cacheCap + queryCap) + 128 * width

theorem extractionWidth_base (width queryCap coeffCap cacheCap : Nat) :
    5 * width ≤ extractionWidth width queryCap coeffCap cacheCap := by
  dsimp [extractionWidth]
  omega

theorem evaluationWidth_le_extractionWidth (width queryCap coeffCap cacheCap innerWidth cap : Nat)
    (hw : innerWidth ≤ 45 * width) (hc : cap ≤ cacheCap + 2 * queryCap) :
    evaluationWidth innerWidth queryCap cap ≤ extractionWidth width queryCap coeffCap cacheCap := by
  have h := Nat.mul_le_mul (show 4 * queryCap + 8 * cap + 64 ≤
    4 * queryCap + 8 * (cacheCap + 2 * queryCap) + 64 by omega) hw
  dsimp [evaluationWidth, extractionWidth, tokenFrameWidth]
  nlinarith only [h]

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem extractionCache_size {value : Ty CryptoAtom}
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width queryCap coeffCap cacheCap cap : Nat) (hh : header ≤ width)
    (hc : ExtractionCache (fun m => Q.size (rep.ty message) m ≤ 5 * width) cap cache)
    (hcap : cap ≤ cacheCap + 2 * queryCap + 1)
    (hv : ∀ f : value.Value (cryptoBase F G₁ G₂ M M), Q.size (rep.ty value) f ≤ 3 * width) :
    Q.size (rep.ty (cacheTy value)) cache ≤ extractionWidth width queryCap coeffCap cacheCap := by
  have h5 : width ≤ 5 * width := by omega
  have h := evaluationCache_size rep sizes lists (value := value) cache (5 * width) queryCap
    (cacheCap + 2 * queryCap + 1) (hh.trans h5)
    (fun p hp => ⟨hc.2 p hp, (hv p.2).trans (by omega)⟩) (hc.1.trans hcap)
  exact h.trans (by dsimp [extractionWidth, tokenFrameWidth, evaluationWidth]; nlinarith)

omit lists in
theorem extraction_target_size
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (width : Nat)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width) :
    Q.size (rep.ty message) output.1 ≤ width := by
  exact (sizes.fst_le (rep.ty message)
    (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) output).trans
      ((sizes.fst_le (rep.ty (AGM.outputTy message)) (rep.env [transcriptTy]) (output, tr, ())).trans hi)

omit lists in
theorem extractionFrames_size {value : Ty CryptoAtom}
    (env : Env (cryptoBase F G₁ G₂ M M) [AGM.outputTy message, transcriptTy])
    (default : (M × G₁) × F) (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) env ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width)
    (hv : ∀ x : value.Value (cryptoBase F G₁ G₂ M M), Q.size (rep.ty value) x ≤ width) :
    Q.size (rep.env [evalRowTy, AGM.outputTy message, transcriptTy]) (default, env) ≤ 3 * width ∧
    (∀ x, Q.size (rep.env [value, evalRowTy, AGM.outputTy message, transcriptTy]) (x, default, env) ≤ 5 * width) ∧
    (∀ x y, Q.size (rep.env [value, value, evalRowTy, AGM.outputTy message, transcriptTy])
      (x, y, default, env) ≤ 7 * width) ∧
    (∀ x y z, Q.size (rep.env [value, value, value, evalRowTy, AGM.outputTy message, transcriptTy])
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

omit lists in
theorem extractionInputs_size
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (width : Nat)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width) :
    Q.size (rep.ty (.list (AGM.tokenTy message))) tr.1 ≤ width ∧
      Q.size (rep.ty (.list (AGM.tokenTy message))) tr.2 ≤ width ∧
      Q.size (rep.ty (.list scalar)) output.2.2.1 ≤ width ∧
      Q.size (rep.ty (.list scalar)) output.2.2.2 ≤ width := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

omit lists in
theorem extractionArgumentFrame_size
    (tokens : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (ht : Q.size (rep.ty (.list (AGM.tokenTy message))) tokens ≤ width)
    (hc : Q.size (rep.ty (.list scalar)) coeff ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width) :
    Q.size (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy])
      (tokens, coeff, default, ()) ≤ 7 * width := by
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.env] at *
  grind only

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]

omit lists in
theorem extraction_default_size (cost : PrimitiveCosts)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (width : Nat)
    (hh : header ≤ width) (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width) :
    Q.size (rep.ty evalRowTy)
      (defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ())) ≤ 5 * width := by
  have hm := extraction_target_size rep sizes output tr width hi
  have hp := @sizes.prod_le
  dsimp only [defaultRow, ReplySyntax.v0, Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty] at *
  grind only

end Signatures.Runtime.LazyAGM
