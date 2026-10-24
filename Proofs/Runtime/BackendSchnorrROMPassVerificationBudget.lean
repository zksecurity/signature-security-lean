import Proofs.Runtime.BackendSchnorrROMPassLocalCost
import Proofs.Runtime.BackendSchnorrROMPassSize

/-! Complete composition of final live hashing with the retained forgery. The
only intermediate premise is the already derived final-hash component budget;
all preparation, copying, packaging and control costs are charged here. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem verify_bound_of_finalHash
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (width tapeWidth mc lc sc rc nextSavedCap bodyTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ width)
    (hs : sc ≤ nextSavedCap) (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hbody : Bounds control queryCost (NativeComponents.finalHash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth mc (lc + 1) nextSavedCap rc) bodyTime) :
    Bounds control queryCost (verify rep data cost primitive sampler)
      (InputBound (Q := Q) rep forgery width width tapeWidth mc lc sc rc)
      (VerifiedBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc)
      (bodyTime + 2061 * overhead (8192 * NativeComponents.frameWidth width mc lc)) := by
  let W := NativeComponents.frameWidth width mc lc
  let fee := overhead (8192 * W)
  let pre := InputBound (Q := Q) rep forgery width width tapeWidth mc lc sc rc
  let nativePre := InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc
  let nativePost := InputBound (Q := Q) rep scalar (3 * width) width tapeWidth mc (lc + 1) nextSavedCap rc
  let post := VerifiedBound (Q := Q) rep width tapeWidth mc (lc + 1) nextSavedCap rc
  let keep := fun out : M × G₁ × F => Q.size (rep.ty forgery) out ≤ width
  have hW : width ≤ W := by
    dsimp [W, NativeComponents.frameWidth]
    nlinarith only [Nat.zero_le ((mc + lc) * width)]
  have hw0 : (6 * (sc + rc) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
  have hin (input) (hi : pre input) : Q.size (rep.ty (withStore forgery)) input ≤ W := by
    have h := input_size rep sizes lists forgery width width tapeWidth mc lc sc rc hh ht (by omega) hw0 input hi
    dsimp [W, NativeComponents.frameWidth]
    nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hn (input) (hi : nativePre input) : Q.size (rep.ty (withStore hashKey)) input ≤ W := by
    have h := input_size rep sizes lists hashKey (3 * width) width tapeWidth mc lc sc rc hh ht (by omega) hw0 input hi
    dsimp [W, NativeComponents.frameWidth]
    nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hout (output) (ho : nativePost output) : Q.size (rep.ty (withStore scalar)) output ≤ W := by
    have h := input_size rep sizes lists scalar (3 * width) width tapeWidth mc (lc + 1) nextSavedCap rc
      hh ht (by omega) hw output ho
    dsimp [W, NativeComponents.frameWidth]
    nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  have hpost (output) (ho : post output) : Q.size (rep.ty (NativeFork.passOutput cachePassOutput)) output ≤ W := by
    have h := verified_size rep sizes lists width tapeWidth mc (lc + 1) nextSavedCap rc hh ht hw output ho
    dsimp [W, NativeComponents.frameWidth]
    nlinarith only [h, Nat.zero_le ((mc + lc) * width)]
  suffices hall : Bounds control queryCost (verify rep data cost primitive sampler) pre post
      (bodyTime + 1028 * fee + 1028 * fee + 5 * overhead (1024 * W)) by
    have hf := mono (show 1024 * W ≤ 8192 * W by omega)
    apply Bounds.time_mono control queryCost hall
    dsimp only [fee, W] at hf ⊢
    omega
  refine wrap_bound rep data cost primitive sizes mono control queryCost routing forgery verifyInput verifyOutput
    _ pre nativePre nativePost post keep W bodyTime (1028 * fee) (1028 * fee) (hh.trans hW)
    hin hn hout (fun _ h => h.trans hW) ?_ ?_ hbody
  · intro input hi
    have hm := (sizes.fst_le (rep.ty message) (rep.ty signatureTy) input.1).trans hi.1
    have hs := (sizes.snd_le (rep.ty message) (rep.ty signatureTy) input.1).trans hi.1
    have hg := (sizes.fst_le (rep.ty point₁) (rep.ty scalar) input.1.2).trans hs
    have hk := sizes.prod_le (rep.ty message) (rep.ty point₁) (input.1.1, input.1.2.1)
    have hkey : Q.size (rep.ty hashKey) (input.1.1, input.1.2.1) ≤ 3 * width := by
      change Q.size (rep.ty hashKey) (input.1.1, input.1.2.1) ≤ _ at hk
      dsimp only at hk
      omega
    refine ⟨⟨⟨hkey, hi.2⟩, hi.1⟩, ?_⟩
    have h := (verifyInput_cost rep data cost primitive sizes lists laws dataLaws mono input W
      (hh.trans hW) (hu.trans hW) (hin input hi)).2
    exact h.trans (Nat.mul_le_mul_left _ (mono (by omega)))
  · intro output ho
    have hp : post (((output.2, output.1.1), output.1.2.1), output.1.2.2) :=
      ⟨⟨ho.2, ho.1.1, ho.1.2.caches⟩, ho.1.2.tape⟩
    refine ⟨hp, ?_, ?_⟩
    · exact hpost _ hp
    · have hi : Q.size (rep.ty (.pair (withStore scalar) forgery)) output ≤ 32 * W := by
        have hn := hout output.1 ho.1
        have hk := ho.2.trans hW
        have hp := sizes.prod_le (rep.ty (withStore scalar)) (rep.ty forgery) output
        change Q.size (rep.ty (.pair (withStore scalar) forgery)) output ≤ _ at hp
        omega
      have h := (verifyOutput_cost rep data cost primitive sizes lists laws dataLaws mono output (32 * W)
        (by omega) (by omega) hi).2
      simpa only [← Nat.mul_assoc, Nat.reduceMul] using h

end Signatures.Runtime.Schnorr.ListROM.NativePass
