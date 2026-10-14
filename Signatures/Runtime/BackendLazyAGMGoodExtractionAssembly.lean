import Signatures.Runtime.BackendLazyAGMExtractionArgs
import Signatures.Runtime.BackendLazyAGMExtractionSize
import Signatures.Runtime.BackendLanguageBudget

/-! Full native good-extractor composition. The two chronological calls and
final private read may change cache invariants; all caller frames, argument
construction, default creation, and final arithmetic are charged here. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

def goodExtractionWith
    (tokens : Program CryptoOp (EvalCmd scalar) [.list (AGM.tokenTy message), .list scalar, evalRowTy] scalar) :
    Program CryptoOp (EvalCmd scalar) [AGM.outputTy message, transcriptTy] scalar :=
  .bind (.ret defaultRow)
    (.bind (.call tokens goodHashArgs)
      (.bind (.call tokens goodSignArgs)
        (.bind (.query .lookup (.fst v3)) (.ret goodExtractResult))))

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

theorem goodExtraction_assembly (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (tokens : Program CryptoOp (EvalCmd scalar) [.list (AGM.tokenTy message), .list scalar, evalRowTy] scalar)
    (output : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) (cache : List (M × F))
    (I₀ I₁ I₂ I₃ : List (M × F) → Prop)
    (width hashTime signTime readTime zeroTime groupZeroTime addTime subTime divTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) (output, tr, ()) ≤ width)
    (hd : Q.size (rep.ty evalRowTy) (defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ())) ≤ width)
    (hcache : I₀ cache)
    (hs₀ : ∀ c, I₀ c → Q.size (rep.ty (cacheTy scalar)) c ≤ width)
    (hs₁ : ∀ c, I₁ c → Q.size (rep.ty (cacheTy scalar)) c ≤ width)
    (hs₂ : ∀ c, I₂ c → Q.size (rep.ty (cacheTy scalar)) c ≤ width)
    (hs₃ : ∀ c, I₃ c → Q.size (rep.ty (cacheTy scalar)) c ≤ width)
    (hhash : ∀ c, I₀ c → ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit)) tokens).run control queryCost
        ((tr.1, output.2.2.1, defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ()), ()), c)),
      I₁ z.value.2 ∧ z.steps ≤ hashTime)
    (hsign : ∀ c, I₁ c → ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit)) tokens).run control queryCost
        ((tr.2, output.2.2.2, defaultRow.denote (arithmetic F G₁ G₂ M M cost) (output, tr, ()), ()), c)),
      I₂ z.value.2 ∧ z.steps ≤ signTime)
    (hread : ∀ c, I₂ c → ∀ z ∈ support ((backendGoodRead rep data cost primitive sampling).run control queryCost (output.1, c)),
      I₃ z.value.2 ∧ z.steps ≤ readTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hgz : (primitiveBound CryptoOp.zero₁).time () ≤ groupZeroTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hsub : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hdiv : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime)
    (out : Run (F × List (M × F)))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit))
      (goodExtractionWith tokens)).run control queryCost ((output, tr, ()), cache))) :
    (Q.size (rep.ty scalar) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy scalar)) out.value.2 ≤ width ∧ I₃ out.value.2) ∧
      out.steps ≤ hashTime + signTime + readTime + zeroTime + groupZeroTime + addTime + subTime + divTime +
        512 * overhead (4096 * width) := by
  let P := arithmetic F G₁ G₂ M M cost
  let env : Env (cryptoBase F G₁ G₂ M M) [AGM.outputTy message, transcriptTy] := (output, tr, ())
  let default := defaultRow.denote P env
  let effect : {a b : Ty CryptoAtom} → EvalCmd scalar a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy scalar)))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy scalar))) :=
    readEffect rep data cost primitive sampling.scalar (.op .zero .unit)
  let pre₀ := fun e => e = env
  let rowOK := fun d => d = default
  let fieldOK := fun (_ : F) => True
  let pre₁ := fun e : Env (cryptoBase F G₁ G₂ M M) [evalRowTy, AGM.outputTy message, transcriptTy] => rowOK e.1 ∧ pre₀ e.2
  let pre₂ := fun e : Env (cryptoBase F G₁ G₂ M M) [scalar, evalRowTy, AGM.outputTy message, transcriptTy] => fieldOK e.1 ∧ pre₁ e.2
  let pre₃ := fun e : Env (cryptoBase F G₁ G₂ M M) [scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy] => fieldOK e.1 ∧ pre₂ e.2
  let pre₄ := fun e : Env (cryptoBase F G₁ G₂ M M) [scalar, scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy] => fieldOK e.1 ∧ pre₃ e.2
  let post := fun p : F × List (M × F) => fieldOK p.1 ∧ I₃ p.2
  let R := overhead (4096 * width)
  let fee := overhead (32 * (16 * width))
  have hw : width ≤ 16 * width := by omega
  have hlocal : overhead (128 * (16 * width)) ≤ R := mono (by omega)
  have hkeyFee : overhead (16 * (16 * width)) ≤ R := mono (by omega)
  have hfee : fee ≤ R := mono (by omega)
  have hframes := extractionFrames_size rep sizes (value := scalar) env default width hh hi hd hf
  have hsize₀ : ∀ e, pre₀ e → Q.size (rep.env [AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    intro e he
    change e = env at he
    rw [he]
    exact hi.trans hw
  have hsize₁ : ∀ e, pre₁ e → Q.size (rep.env [evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨d, e⟩ hp
    have hd' : d = default := hp.1
    have he : e = env := hp.2
    rw [hd', he]
    exact hframes.1.trans (by omega)
  have hsize₂ : ∀ e, pre₂ e → Q.size (rep.env [scalar, evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨h, d, e⟩ hp
    have hd' : d = default := hp.2.1
    have he : e = env := hp.2.2
    rw [hd', he]
    exact (hframes.2.1 h).trans (by omega)
  have hsize₃ : ∀ e, pre₃ e → Q.size (rep.env [scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨s, h, d, e⟩ hp
    have hd' : d = default := hp.2.2.1
    have he : e = env := hp.2.2.2
    rw [hd', he]
    exact (hframes.2.2.1 s h).trans (by omega)
  have hsize₄ : ∀ e, pre₄ e → Q.size (rep.env [scalar, scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy]) e ≤ 16 * width := by
    rintro ⟨t, s, h, d, e⟩ hp
    have hd' : d = default := hp.2.2.2.1
    have he : e = env := hp.2.2.2.2
    rw [hd', he]
    exact (hframes.2.2.2 t s h).trans (by omega)
  have hinputs := extractionInputs_size rep sizes output tr width hi
  have hhashArgs := extractionArgumentFrame_size rep sizes tr.1 output.2.2.1 default width hh hu hinputs.1 hinputs.2.2.1 hd
  have hsignArgs := extractionArgumentFrame_size rep sizes tr.2 output.2.2.2 default width hh hu hinputs.2.1 hinputs.2.2.2 hd
  have htarget := extraction_target_size rep sizes output tr width hi
  have hdefault := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect defaultRow pre₀ rowOK I₀ (16 * width)
    (zeroTime + groupZeroTime + 32 * R) hsize₀ (fun c hc => (hs₀ c hc).trans hw)
    (by intro e he; change e = env at he; rw [he]; exact ⟨rfl, hd.trans hw⟩)
    (by
      intro e he
      have h := defaultRow_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e (16 * width)
        zeroTime groupZeroTime (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) (hg.trans hw) (hsize₀ e he) hz hgz
      exact h.trans (by omega))
  have hhashCall := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect tokens goodHashArgs pre₁
    (fun args => args = (tr.1, output.2.2.1, default, ())) I₀ (fun p => fieldOK p.1 ∧ I₁ p.2)
    (16 * width) (64 * R) hashTime (hh.trans hw) hsize₁ (fun c hc => (hs₀ c hc).trans hw)
    (by
      rintro ⟨d, e⟩ hp
      have hd' : d = default := hp.1
      have he : e = env := hp.2
      rw [hd', he]
      exact ⟨rfl, hhashArgs.trans (by omega)⟩)
    (by intro e he; exact (goodHashArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) (hh.trans hw) (hu.trans hw) (hsize₁ e he)).trans (by omega))
    (by
      rintro ⟨args, c⟩ hp z hz'
      have heq : args = (tr.1, output.2.2.1, default, ()) := hp.1
      rw [heq] at hz'
      have h := hhash c hp.2 z hz'
      exact ⟨⟨trivial, h.1⟩, h.2⟩)
  have hsignCall := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect tokens goodSignArgs pre₂
    (fun args => args = (tr.2, output.2.2.2, default, ())) I₁ (fun p => fieldOK p.1 ∧ I₂ p.2)
    (16 * width) (64 * R) signTime (hh.trans hw) hsize₂ (fun c hc => (hs₁ c hc).trans hw)
    (by
      rintro ⟨h, d, e⟩ hp
      have hd' : d = default := hp.2.1
      have he : e = env := hp.2.2
      rw [hd', he]
      exact ⟨rfl, hsignArgs.trans (by omega)⟩)
    (by intro e he; exact (goodSignArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) (hh.trans hw) (hu.trans hw) (hsize₂ e he)).trans (by omega))
    (by
      rintro ⟨args, c⟩ hp z hz'
      have heq : args = (tr.2, output.2.2.2, default, ()) := hp.1
      rw [heq] at hz'
      have h := hsign c hp.2 z hz'
      exact ⟨⟨trivial, h.1⟩, h.2⟩)
  have hquery := Language.query_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect EvalCmd.lookup (.fst v3) pre₃ (fun m => m = output.1) I₂ post
    (16 * width) (9 * R) readTime (hh.trans hw) hsize₃ (fun c hc => (hs₂ c hc).trans hw)
    (by
      rintro ⟨s, h, d, e⟩ hp
      have he : e = env := hp.2.2.2
      rw [he]
      exact ⟨rfl, htarget.trans hw⟩)
    (by intro e he; exact (goodTarget_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) (hsize₃ e he)).trans (by omega))
    (by
      rintro ⟨m, c⟩ hp z hz'
      have hm : m = output.1 := hp.1
      rw [hm] at hz'
      have h := hread c hp.2 z (by rw [backendGoodRead]; exact hz')
      exact ⟨⟨trivial, h.1⟩, h.2⟩)
  have hfinish := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect goodExtractResult pre₄ fieldOK I₃ (16 * width)
    (addTime + subTime + divTime + 64 * R) hsize₄ (fun c hc => (hs₃ c hc).trans hw)
    (by intro e _; exact ⟨trivial, (hf _).trans hw⟩)
    (by intro e he; exact (goodExtractResult_cost rep data cost primitive laws dataLaws primitiveBound sizes mono e
      (16 * width) addTime subTime divTime (hh.trans hw) (hsize₄ e he) (fun f => (hf f).trans hw) ha hsub hdiv).trans (by omega))
  have htail₃ := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect (.query .lookup (.fst v3)) (.ret goodExtractResult)
    pre₃ fieldOK I₂ I₃ post (16 * width) (9 * R + readTime + 3 * fee)
    (addTime + subTime + divTime + 64 * R + 2 * fee) (hh.trans hw) hsize₃
    (fun f _ => (hf f).trans hw) (fun c hc => (hs₂ c hc).trans hw) (fun c hc => (hs₃ c hc).trans hw) hquery hfinish
  have htail₂ := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect (.call tokens goodSignArgs) (.bind (.query .lookup (.fst v3)) (.ret goodExtractResult))
    pre₂ fieldOK I₁ I₂ post (16 * width) (64 * R + signTime + 3 * fee)
    ((9 * R + readTime + 3 * fee) + (addTime + subTime + divTime + 64 * R + 2 * fee) + 20 * fee)
    (hh.trans hw) hsize₂ (fun f _ => (hf f).trans hw) (fun c hc => (hs₁ c hc).trans hw)
    (fun c hc => (hs₂ c hc).trans hw) hsignCall htail₃
  have htail₁ := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect (.call tokens goodHashArgs)
    (.bind (.call tokens goodSignArgs) (.bind (.query .lookup (.fst v3)) (.ret goodExtractResult)))
    pre₁ fieldOK I₀ I₁ post (16 * width) (64 * R + hashTime + 3 * fee)
    ((64 * R + signTime + 3 * fee) + ((9 * R + readTime + 3 * fee) +
      (addTime + subTime + divTime + 64 * R + 2 * fee) + 20 * fee) + 20 * fee)
    (hh.trans hw) hsize₁ (fun f _ => (hf f).trans hw) (fun c hc => (hs₀ c hc).trans hw)
    (fun c hc => (hs₁ c hc).trans hw) hhashCall htail₂
  have hfull := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy scalar)) effect (.ret defaultRow)
    (.bind (.call tokens goodHashArgs) (.bind (.call tokens goodSignArgs) (.bind (.query .lookup (.fst v3)) (.ret goodExtractResult))))
    pre₀ rowOK I₀ post (16 * width) (zeroTime + groupZeroTime + 32 * R + 2 * fee)
    ((64 * R + hashTime + 3 * fee) + ((64 * R + signTime + 3 * fee) +
      ((9 * R + readTime + 3 * fee) + (addTime + subTime + divTime + 64 * R + 2 * fee) + 20 * fee) + 20 * fee) + 20 * fee)
    (hh.trans hw) hsize₀ (by intro d hd'; change d = default at hd'; rw [hd']; exact hd.trans hw)
    (fun c hc => (hs₀ c hc).trans hw) hdefault htail₁
  have h := hfull (env, cache) ⟨rfl, hcache⟩ out hout
  exact ⟨⟨hf _, hs₃ _ h.1.2, h.1.2⟩, by dsimp only [R, fee] at *; omega⟩

end Signatures.Runtime.LazyAGM
