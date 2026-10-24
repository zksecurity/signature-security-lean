import Proofs.Runtime.BackendListLength
import Proofs.Runtime.Extraction

/-! The representation-size obligation for attacker-supplied coefficients.
Each list length is recovered from the complete encoded output, including any
surplus coefficients. The proof uses a positive-cell encoding contract; upper
list-size bounds or transcript lengths alone cannot supply this conclusion.
-/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type} {messageTy : Ty CryptoAtom}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lengths : ListLengthLaws Q rep.data)

include sizes lengths

theorem coefficient_lengths_le_output
    (out : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    out.2.2.1.length ≤ Q.size (rep.ty (AGM.outputTy messageTy)) out ∧
      out.2.2.2.length ≤ Q.size (rep.ty (AGM.outputTy messageTy)) out := by
  have hbody := sizes.snd_le (rep.ty messageTy)
    (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar)))) out
  have hpair := sizes.snd_le (rep.ty scalar)
    (rep.ty (.pair (.list scalar) (.list scalar))) out.2
  have hgamma := sizes.fst_le (rep.ty (.list scalar)) (rep.ty (.list scalar)) out.2.2
  have hxi := sizes.snd_le (rep.ty (.list scalar)) (rep.ty (.list scalar)) out.2.2
  have lg := lengths.length_le_size (rep.ty scalar) out.2.2.1
  have lx := lengths.length_le_size (rep.ty scalar) out.2.2.2
  dsimp only [AGM.outputTy, LanguageRepresentation.ty] at *
  omega

theorem coefficient_lengths_of_output_cap
    (out : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) (cap : Nat)
    (ho : Q.size (rep.ty (AGM.outputTy messageTy)) out ≤ cap) :
    (AGM.outputView out).γ.length ≤ cap ∧ (AGM.outputView out).ξ.length ≤ cap ∧
      (AGM.outputView out).γ.length + (AGM.outputView out).ξ.length ≤ 2 * cap := by
  have h := coefficient_lengths_le_output rep sizes lengths out
  dsimp only [AGM.outputView]
  omega

end Signatures.Runtime.WeightedAGM
