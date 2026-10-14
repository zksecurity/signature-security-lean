import Signatures.Runtime.BackendLazyAGMExtractionArgs
import Signatures.Runtime.BackendLazyAGMExtractionSize
import Signatures.Runtime.BackendLanguageBudget

/-! Full native bad-extractor composition, retaining the entire attacker output
and both transcripts while executing the signing evaluation, target pair read,
and original field extraction. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

def badExtractionWith
    (tokens : Program CryptoOp (EvalCmd (.pair scalar scalar))
      [.list (AGM.tokenTy message), .list scalar, evalRowTy] (.pair scalar scalar)) :
    Program CryptoOp (EvalCmd (.pair scalar scalar)) [AGM.outputTy message, transcriptTy] scalar :=
  .bind (.ret defaultRow)
    (.bind (.call tokens badSignArgs)
      (.bind (.query .lookup (.fst v2)) (.ret badExtractResult)))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes mono routing

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem badExtraction_assembly (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (tokens : Program CryptoOp (EvalCmd (.pair scalar scalar))
      [.list (AGM.tokenTy message), .list scalar, evalRowTy] (.pair scalar scalar))
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × (F × F)))
    (I₀ I₁ I₂ : List (M × (F × F)) → Prop)
    (width signTime readTime zeroTime groupZeroTime subTime negTime divTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hp : ∀ p : F × F, Q.size (rep.ty (.pair scalar scalar)) p ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width)
    (hd : Q.size (rep.ty evalRowTy) (defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ())) ≤ width)
    (hcache : I₀ cache)
    (hs₀ : ∀ c, I₀ c → Q.size (rep.ty (cacheTy (.pair scalar scalar))) c ≤ width)
    (hs₁ : ∀ c, I₁ c → Q.size (rep.ty (cacheTy (.pair scalar scalar))) c ≤ width)
    (hs₂ : ∀ c, I₂ c → Q.size (rep.ty (cacheTy (.pair scalar scalar))) c ≤ width)
    (hsign : ∀ c, I₀ c → ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy (.pair scalar scalar)))
      (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))) tokens).run control queryCost
        ((tr.2, output.2.2.2, defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ()), ()), c)),
      I₁ z.value.2 ∧ z.steps ≤ signTime)
    (hread : ∀ c, I₁ c → ∀ z ∈ support ((backendBadRead rep data cost primitive sampling).run control queryCost (output.1, c)),
      I₂ z.value.2 ∧ z.steps ≤ readTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hgz : (primitiveBound CryptoOp.zero₁).time () ≤ groupZeroTime)
    (hsub : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hneg : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ negTime)
    (hdiv : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime)
    (out : Run (F × List (M × (F × F))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy (.pair scalar scalar)))
      (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit)))
      (badExtractionWith tokens)).run control queryCost ((output, tr, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy (.pair scalar scalar))) out.value.2 ≤ width ∧ I₂ out.value.2) ∧
      out.steps ≤ signTime + readTime + zeroTime + groupZeroTime + 2 * subTime + negTime + divTime +
        512 * overhead (4096 * width) := by
  let P := arithmetic F G₁ G₂ M M cost
  let env : Env (cryptoBase F G₁ G₂ M M) [AGM.outputTy message, transcriptTy] := (output, tr, ())
  let default := defaultRow.denote P env
  let effect : {a b : Ty CryptoAtom} → EvalCmd (.pair scalar scalar) a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy (.pair scalar scalar))))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy (.pair scalar scalar)))) :=
    readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
  let pre₀ := fun e => e = env
  let rowOK := fun d => d = default
  let pairOK := fun (_ : F × F) => True
  let fieldOK := fun (_ : F) => True
  let pre₁ := fun e : Env (cryptoBase F G₁ G₂ M M) [evalRowTy, AGM.outputTy message, transcriptTy] => rowOK e.1 ∧ pre₀ e.2
  let pre₂ := fun e : Env (cryptoBase F G₁ G₂ M M) [.pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy] => pairOK e.1 ∧ pre₁ e.2
  let pre₃ := fun e : Env (cryptoBase F G₁ G₂ M M) [.pair scalar scalar, .pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy] => pairOK e.1 ∧ pre₂ e.2
  let post := fun p : F × List (M × (F × F)) => fieldOK p.1 ∧ I₂ p.2
  let R := overhead (4096 * width)
  let fee := overhead (32 * (16 * width))
  have hw : width ≤ 16 * width := by omega
  have hlocal : overhead (128 * (16 * width)) ≤ R := mono (by omega)
  have hkeyFee : overhead (16 * (16 * width)) ≤ R := mono (by omega)
  have hfee : fee ≤ R := mono (by omega)
  have hframes := extractionFrames_size rep sizes (value := .pair scalar scalar) env default width hh hi hd hp
  have hsize₀ : ∀ e, pre₀ e → Q.size (rep.env [AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    intro e he
    change e = env at he
    rw [he]
    exact hi.trans hw
  have hsize₁ : ∀ e, pre₁ e → Q.size (rep.env [evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨d, e⟩ hp'
    have hd' : d = default := hp'.1
    have he : e = env := hp'.2
    rw [hd', he]
    exact hframes.1.trans (by omega)
  have hsize₂ : ∀ e, pre₂ e → Q.size (rep.env [.pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨s, d, e⟩ hp'
    have hd' : d = default := hp'.2.1
    have he : e = env := hp'.2.2
    rw [hd', he]
    exact (hframes.2.1 s).trans (by omega)
  have hsize₃ : ∀ e, pre₃ e → Q.size (rep.env [.pair scalar scalar, .pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨t, s, d, e⟩ hp'
    have hd' : d = default := hp'.2.2.1
    have he : e = env := hp'.2.2.2
    rw [hd', he]
    exact (hframes.2.2.1 t s).trans (by omega)
  have hinputs := extractionInputs_size rep sizes output tr width hi
  have hsignArgs := extractionArgumentFrame_size rep sizes tr.2 output.2.2.2 default width hh hu hinputs.2.1 hinputs.2.2.2 hd
  have htarget := extraction_target_size rep sizes output tr width hi
  have hdefault := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect defaultRow pre₀ rowOK I₀ (16 * width)
    (zeroTime + groupZeroTime + 32 * R) hsize₀ (fun c hc => (hs₀ c hc).trans hw)
    (by intro e he; change e = env at he; rw [he]; exact ⟨rfl, hd.trans hw⟩)
    (by
      intro e he
      have h := defaultRow_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e (16 * width)
        zeroTime groupZeroTime (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) (hg.trans hw) (hsize₀ e he) hz hgz
      exact h.trans (by omega))
  have hsignCall := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect tokens badSignArgs pre₁
    (fun args => args = (tr.2, output.2.2.2, default, ())) I₀ (fun p => pairOK p.1 ∧ I₁ p.2)
    (16 * width) (64 * R) signTime (hh.trans hw) hsize₁ (fun c hc => (hs₀ c hc).trans hw)
    (by
      rintro ⟨d, e⟩ hp'
      have hd' : d = default := hp'.1
      have he : e = env := hp'.2
      rw [hd', he]
      exact ⟨rfl, hsignArgs.trans (by omega)⟩)
    (by intro e he; exact (badSignArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) (hh.trans hw) (hu.trans hw) (hsize₁ e he)).trans (by omega))
    (by
      rintro ⟨args, c⟩ hp' z hz'
      have heq : args = (tr.2, output.2.2.2, default, ()) := hp'.1
      rw [heq] at hz'
      have h := hsign c hp'.2 z hz'
      exact ⟨⟨trivial, h.1⟩, h.2⟩)
  have hquery := Language.query_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect EvalCmd.lookup (.fst v2) pre₂ (fun m => m = output.1) I₁
    (fun p => pairOK p.1 ∧ I₂ p.2) (16 * width) (7 * R) readTime (hh.trans hw) hsize₂ (fun c hc => (hs₁ c hc).trans hw)
    (by
      rintro ⟨s, d, e⟩ hp'
      have he : e = env := hp'.2.2
      rw [he]
      exact ⟨rfl, htarget.trans hw⟩)
    (by intro e he; exact (badTarget_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) (hsize₂ e he)).trans (by omega))
    (by
      rintro ⟨m, c⟩ hp' z hz'
      have hm : m = output.1 := hp'.1
      rw [hm] at hz'
      have h := hread c hp'.2 z (by rw [backendBadRead]; exact hz')
      exact ⟨⟨trivial, h.1⟩, h.2⟩)
  have hfinish := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect badExtractResult pre₃ fieldOK I₂ (16 * width)
    (2 * subTime + negTime + divTime + 64 * R) hsize₃ (fun c hc => (hs₂ c hc).trans hw)
    (by intro e _; exact ⟨trivial, (hf _).trans hw⟩)
    (by intro e he; exact (badExtractResult_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) subTime negTime divTime (hh.trans hw) (hsize₃ e he) (fun f => (hf f).trans hw) hsub hneg hdiv).trans (by omega))
  have htail₂ := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect (.query .lookup (.fst v2)) (.ret badExtractResult)
    pre₂ pairOK I₁ I₂ post (16 * width) (7 * R + readTime + 3 * fee)
    (2 * subTime + negTime + divTime + 64 * R + 2 * fee) (hh.trans hw) hsize₂
    (fun p _ => (hp p).trans hw) (fun c hc => (hs₁ c hc).trans hw) (fun c hc => (hs₂ c hc).trans hw) hquery hfinish
  have htail₁ := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect (.call tokens badSignArgs) (.bind (.query .lookup (.fst v2)) (.ret badExtractResult))
    pre₁ pairOK I₀ I₁ post (16 * width) (64 * R + signTime + 3 * fee)
    ((7 * R + readTime + 3 * fee) + (2 * subTime + negTime + divTime + 64 * R + 2 * fee) + 20 * fee)
    (hh.trans hw) hsize₁ (fun p _ => (hp p).trans hw) (fun c hc => (hs₀ c hc).trans hw)
    (fun c hc => (hs₁ c hc).trans hw) hsignCall htail₂
  have hfull := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy (.pair scalar scalar))) effect (.ret defaultRow)
    (.bind (.call tokens badSignArgs) (.bind (.query .lookup (.fst v2)) (.ret badExtractResult)))
    pre₀ rowOK I₀ post (16 * width) (zeroTime + groupZeroTime + 32 * R + 2 * fee)
    ((64 * R + signTime + 3 * fee) + ((7 * R + readTime + 3 * fee) +
      (2 * subTime + negTime + divTime + 64 * R + 2 * fee) + 20 * fee) + 20 * fee)
    (hh.trans hw) hsize₀ (by intro d hd'; change d = default at hd'; rw [hd']; exact hd.trans hw)
    (fun c hc => (hs₀ c hc).trans hw) hdefault htail₁
  have h := hfull (env, cache) ⟨rfl, hcache⟩ out hout
  exact ⟨⟨hf _, hs₂ _ h.1.2, h.1.2⟩, by dsimp only [R, fee] at *; omega⟩

end Signatures.Runtime.LazyAGM
