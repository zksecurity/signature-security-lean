import Signatures.Runtime.BackendSchnorrNonzeroSigning
import Signatures.Runtime.BackendSchnorrROMProgrammingCost

/-! Connect the implemented signing routine to the nonzero source simulator,
including the programmed cache. Sampling laws are supplied for the two original
samplers; no secret key or discrete-log computation is used by the routine. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroSigning

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- Sample the established nonzero transcript and program its repaired target,
preserving an existing cached value on collision. -/
def source (g pk : G₁) (msg : M) (cache : List ((M × G₁) × F)) :
    ProbComp ((G₁ × F) × List ((M × G₁) × F)) := do
  let transcript ← _root_.Schnorr.NonzeroNonce.simTranscript g pk
  pure ((transcript.1, transcript.2.2), CacheProgramming.value (msg, transcript.1) transcript.2.1 cache)

theorem body_source {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (cost : PrimitiveCosts) (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd ProbComp)
    (fieldDraw nonzeroDraw : Cmd .unit scalar)
    (hField : H fieldDraw () = ($ᵗ F))
    (hNonzero : H nonzeroDraw () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
    (g pk : G₁) (msg : M) (cache : List ((M × G₁) × F)) :
    (body fieldDraw nonzeroDraw).denote (arithmetic F G₁ G₂ K M cost) H (msg, g, pk, cache, ()) =
      source g pk msg cache := by
  rw [body_denote (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost H fieldDraw nonzeroDraw msg g pk cache]
  simp only [hField, hNonzero, bind_map_left, source,
    _root_.Schnorr.NonzeroNonce.simTranscript, bind_assoc]
  congr 1
  funext c
  congr 1
  funext z
  congr 1
  funext a
  by_cases h : z • g - c • pk = 0 <;>
    simp only [h, ↓reduceIte, pure_bind,
      ListROM.NativeCache.programming_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost]

namespace Native

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}

/-- With the original sampler laws, the actual compiled signing program has
exactly the source simulator's signature/cache computation, including draw order. -/
theorem code_source
    (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
    (data : DataCode Q rep.data) (cost : PrimitiveCosts)
    (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
      Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
    (fieldDraw nonzeroDraw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit rep.data.unit)
      (StepClass.HasProd.prod (rep.ty scalar) rep.data.unit))
    (hField : fieldDraw.denote ((), ()) = (fun c : F => (c, ())) <$> ($ᵗ F))
    (hNonzero : nonzeroDraw.denote ((), ()) = (fun a : Fˣ => ((a : F), ())) <$> ($ᵗ Fˣ))
    (g pk : G₁) (msg : M) (cache : List ((M × G₁) × F)) :
    (code rep data cost primitive rep.data.unit fieldDraw nonzeroDraw).denote ((msg, g, pk, cache, ()), ()) =
      (fun result => (result, ())) <$> source g pk msg cache := by
  rw [code_denote]
  simp only [hField, hNonzero, bind_map_left, source,
    _root_.Schnorr.NonzeroNonce.simTranscript, bind_assoc, map_bind, map_pure]
  congr 1
  funext c
  congr 1
  funext z
  congr 1
  funext a
  by_cases h : z • g - c • pk = 0 <;>
    simp only [h, ↓reduceIte, pure_bind,
      ListROM.NativeCache.programming_value (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost]

end Native

end Signatures.Runtime.Schnorr.NonzeroSigning
