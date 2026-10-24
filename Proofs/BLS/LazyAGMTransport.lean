import Proofs.BLS.LazyAGMFiniteMessages
import Proofs.BLS.CoCDH.CacheTransport

/-! Exact message renaming for adaptive AGM execution and sparse extraction.
Renaming preserves reply occurrences and coefficients, not just final outputs. -/

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.Reduction
open BLS.CoCDH.MessageTransport

namespace BLS.LazyAGM.MessageTransport

variable {F N M R G₁ G₂ α : Type}

def mapTranscript (f : N → M) (tr : Transcript N N G₁) : Transcript M M G₁ :=
  (tr.1.map (Prod.map f id), tr.2.map (Prod.map f id))

@[simp] theorem mapTranscript_empty (f : N → M) :
    mapTranscript (G₁ := G₁) f ([], []) = ([], []) := rfl

@[simp] theorem mapTranscript_hash (f : N → M) (tr : Transcript N N G₁) (n : N) (r : G₁) :
    mapTranscript f (tr.1 ++ [(n, r)], tr.2) =
      ((mapTranscript f tr).1 ++ [(f n, r)], (mapTranscript f tr).2) := by
  simp [mapTranscript]

@[simp] theorem mapTranscript_sign (f : N → M) (tr : Transcript N N G₁) (n : N) (r : G₁) :
    mapTranscript f (tr.1, tr.2 ++ [(n, r)]) =
      ((mapTranscript f tr).1, (mapTranscript f tr).2 ++ [(f n, r)]) := by
  simp [mapTranscript]

theorem privateOracle_random (hash sign : R → G₁) (n : Nat) (tr : Transcript M M G₁) :
    ((privateOracle hash sign) (.inl (.inl n))).run tr =
      (fun r => (r, tr)) <$>
        (liftM ((baseSpec M R).query (.inl n)) : OracleComp (baseSpec M R) (Fin (n + 1))) := by
  simp [privateOracle, handler]

theorem privateOracle_hash (hash sign : R → G₁) (m : M) (tr : Transcript M M G₁) :
    ((privateOracle hash sign) (.inl (.inr m))).run tr =
      (fun r => (hash r, (tr.1 ++ [(m, hash r)], tr.2))) <$>
        (liftM ((baseSpec M R).query (.inr m)) : OracleComp (baseSpec M R) R) := by
  simp [privateOracle, handler]

theorem privateOracle_sign (hash sign : R → G₁) (m : M) (tr : Transcript M M G₁) :
    ((privateOracle hash sign) (.inr m)).run tr =
      (fun r => (sign r, (tr.1, tr.2 ++ [(m, sign r)]))) <$>
        (liftM ((baseSpec M R).query (.inr m)) : OracleComp (baseSpec M R) R) := by
  simp [privateOracle, handler]

theorem privateSim_map (f : N → M) (hash sign : R → G₁)
    (oa : OracleComp (advSpec N N G₁) α) (tr : Transcript N N G₁) :
    (simulateQ (privateOracle hash sign) (simulateQ (CoCDH.Tight.messageQueries f) oa)).run
        (mapTranscript f tr) =
      Prod.map id (mapTranscript f) <$>
        simulateQ (baseQueries f) ((simulateQ (privateOracle hash sign) oa).run tr) := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure a => simp
  | query_bind q next ih =>
    rcases q with ((n | m) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, CoCDH.Tight.messageQueries,
        simulateQ_HasQuery_query, StateT.run_bind, privateOracle_random,
        privateOracle_hash, privateOracle_sign, bind_map_left, baseQueries, map_bind]
    · exact bind_congr fun r => ih r tr
    · exact bind_congr fun r => by simpa only [mapTranscript_hash] using ih (hash r) (tr.1 ++ [(m, hash r)], tr.2)
    · exact bind_congr fun r => by simpa only [mapTranscript_sign] using ih (sign r) (tr.1, tr.2 ++ [(m, sign r)])

theorem privateRun_map (f : N → M) (hash sign : R → G₁)
    (A : Adversary F N N G₁ G₂) (pk : G₂) :
    privateRun hash sign (mapAdversary f A) pk =
      Prod.map (mapOutput f) (mapTranscript f) <$>
        simulateQ (baseQueries f) (privateRun hash sign A pk) := by
  unfold privateRun mapAdversary mapMain
  simp only [simulateQ_map, StateT.run_map]
  rw [← mapTranscript_empty f, privateSim_map]
  simp only [Functor.map_map]
  congr 1

theorem traceTerms_map [Zero F] (f : N → M) (coeff : List F) (tr : List (N × G₁)) :
    traceTerms coeff (tr.map (Prod.map f id)) = (traceTerms coeff tr).map (Prod.map f id) := by
  simp [traceTerms, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

theorem evalTerms_map [AddCommMonoid R] [SMul F R] (f : N → M) (terms : List (N × F)) :
    evalTerms (G₁ := R) (terms.map (Prod.map f id)) =
      simulateQ (baseQueries f) (evalTerms (G₁ := R) terms) := by
  induction terms with
  | nil => simp [evalTerms]
  | cons p rest ih =>
    rcases p with ⟨n, c⟩
    simp [evalTerms, baseQueries, ih]

variable [Field F] [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_map (f : N → M) (g X : G₁) (pk : G₂) (A : Adversary F N N G₁ G₂) :
    goodProgram g X pk (mapAdversary f A) =
      simulateQ (baseQueries f) (goodProgram g X pk A) := by
  simp [goodProgram, privateRun_map, mapOutput, mapTranscript, traceTerms_map,
    evalTerms_map, baseQueries, bind_map_left]

theorem badProgram_map (f : N → M) (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F N N G₁ G₂) :
    badProgram g X pk kappa (mapAdversary f A) =
      simulateQ (baseQueries f) (badProgram g X pk kappa A) := by
  simp [badProgram, privateRun_map, mapOutput, mapTranscript, traceTerms_map,
    evalTerms_map, baseQueries, bind_map_left]

variable [SampleableType F] [DecidableEq N] [DecidableEq M]

theorem goodReduction_map (f : N → M) (hf : Function.Injective f)
    (A : Adversary F N N G₁ G₂) :
    goodReductionLazy (mapAdversary f A) = goodReductionLazy A := by
  funext g X g₂ pk
  unfold goodReductionLazy
  rw [goodProgram_map, lazyRun_rename f hf]

variable [AddCommGroup G₂] [Module F G₂]

theorem badReduction_map (f : N → M) (hf : Function.Injective f)
    (A : Adversary F N N G₁ G₂) :
    badReductionLazy (mapAdversary f A) = badReductionLazy A := by
  funext g X g₂ pk
  unfold badReductionLazy
  apply bind_congr
  intro kappa
  rw [badProgram_map, lazyRun_rename f hf]

end BLS.LazyAGM.MessageTransport
