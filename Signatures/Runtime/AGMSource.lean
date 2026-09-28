import Signatures.Runtime.AGMSimulation
import Signatures.Runtime.Extraction

/-! Implementation certificates for AGM source adversaries. Code receives exactly the public
key and its fixed first-order data, never the simulator's private tables or challenge fields.
Both semantic and all-path resource obligations hold for every public key. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

def decodeOutput {F G₁ G₂ K M N : Type} {messageTy : Ty CryptoAtom}
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N)
    (out : (outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) : Model.LazyAGM.Output F N :=
  ⟨message out.1, out.2.1, out.2.2.1, out.2.2.2⟩

variable {F G₁ G₂ K M I N : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {indexTy messageTy : Ty CryptoAtom}

/-- Fixed data may itself contain arbitrary nested pairs/lists; its structural load is
charged by the final target package. Reply prices are universally quantified so the source
certificate covers every adaptive path, not just a chosen simulation or game. -/
structure SourceCertificate (cost : PrimitiveCosts)
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N)
    (randomBound localTime : Nat) (queries : Fin 3 → Nat) (gammaLength xiLength : Nat)
    (adv : Model.LazyAGM.Adversary F I N G₁ G₂) where
  dataTy : Ty CryptoAtom
  data : dataTy.Value (cryptoBase F G₁ G₂ K M)
  code : Program CryptoOp (Command indexTy messageTy randomBound)
    [point₂, dataTy] (outputTy messageTy)
  semantics : ∀ pk : G₂,
    decodeOutput message <$> code.denote (arithmetic F G₁ G₂ K M cost)
      (sourceSemantics index message randomBound) (pk, data, ()) = adv.main pk
  budget : ∀ pk : G₂,
    SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
      code (pk, data, ()) localTime queries
  outputSizes : ∀ (pk : G₂) (price : Fin 3 → Nat) z,
    z ∈ support (code.run (arithmetic F G₁ G₂ K M cost)
      (pricedRequests (replies randomBound) (fun cmd => price (kind cmd))) (pk, data, ())) →
    z.value.2.2.1.length ≤ gammaLength ∧ z.value.2.2.2.length ≤ xiLength

variable [SampleableType F]
  {cost : PrimitiveCosts}
  {index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I}
  {message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N}
  {randomBound localTime gammaLength xiLength : Nat} {queries : Fin 3 → Nat}
  {adv : Model.LazyAGM.Adversary F I N G₁ G₂}

theorem SourceCertificate.simulated_output_sizes
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    {configTy : Ty CryptoAtom} (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁) (cHash cSign : Nat)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (hHash : ∀ i, (hash.run (arithmetic F G₁ G₂ K M cost) (i, cfg, ())).steps ≤ cHash)
    (hSign : ∀ m, (sign.run (arithmetic F G₁ G₂ K M cost) (m, cfg, ())).steps ≤ cSign)
    (pk : G₂) (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (z : Run ((outputTy messageTy).Value (cryptoBase F G₁ G₂ K M)) ×
      (oracleStore indexTy messageTy configTy).Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support (((cert.code.inline (machineRoutines hash sign randomBound)).run
      (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling (oracleStore indexTy messageTy configTy))
      (pk, cert.data, ())).run (cfg, tr))) :
    z.1.value.2.2.1.length ≤ gammaLength ∧ z.1.value.2.2.2.length ≤ xiLength := by
  obtain ⟨r, hr, hv⟩ := machineSimulation_supported cost sampling hash sign randomBound
    cHash cSign cfg hHash hSign cert.code (pk, cert.data, ()) tr z hz
  simpa only [hv] using cert.outputSizes pk (machinePrices sampling randomBound cHash cSign) r hr

/-- The full adaptive source trace, including decoded output and chronological explicit
replies, is exactly the native fixed-run experiment at the actual supplied public key. -/
theorem SourceCertificate.simulation_erase
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    {configTy : Ty CryptoAtom} (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁)
    (H : configTy.Value (cryptoBase F G₁ G₂ K M) → I → G₁)
    (S : configTy.Value (cryptoBase F G₁ G₂ K M) → N → G₁)
    (hHash : ∀ cfg i, hash.denote (arithmetic F G₁ G₂ K M cost) (i, cfg, ()) = H cfg (index i))
    (hSign : ∀ cfg m, sign.denote (arithmetic F G₁ G₂ K M cost) (m, cfg, ()) = S cfg (message m))
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M)) (pk : G₂) :
    (fun z => (decodeOutput message z.1.value, transcriptView index message z.2.2)) <$>
      (((cert.code.inline (machineRoutines hash sign randomBound)).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy configTy))
        (pk, cert.data, ())).run (cfg, [], [])) =
      Model.LazyAGM.fixedRun adv pk (H cfg) (S cfg) := by
  have h := machineSimulation_erase cost sampling hash sign index message H S hHash hSign
    randomBound cert.code (pk, cert.data, ()) cfg ([], [])
  have he := congrArg (Functor.map (fun z => (decodeOutput message z.1, z.2))) h
  have hn : (fun z => (decodeOutput message z.1, z.2)) <$>
    (simulateQ (Model.LazyAGM.fixedImpl (H cfg) (S cfg))
      (cert.code.denote (arithmetic F G₁ G₂ K M cost) (sourceSemantics index message randomBound)
        (pk, cert.data, ()))).run ([], []) = Model.LazyAGM.fixedRun adv pk (H cfg) (S cfg) := by
    rw [← StateT.run_map, ← simulateQ_map, cert.semantics]
    rfl
  simpa only [Functor.map_map, Function.comp_def, transcriptView, List.reverse_nil, List.map_nil] using
    he.trans hn

end Signatures.Runtime.AGM
