import Signatures.LinearFunctional.Proofs.LazyAGMCoupling
import Signatures.BLS.Proofs.LazyAGMTransport

/-! Exact renaming of both weighted-base indices and signed messages. This
preserves every adaptive reply and coefficient occurrence. The two maps need
not coincide; the scheme's weighted term lists must commute with them. -/

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedReduction
open BLS.CoCDH.MessageTransport
open BLS.LazyAGM.MessageTransport (mapOutput traceTerms_map evalTerms_map)

namespace Model.LazyAGM.WeightedTransport

variable {F ι κ M N R G₁ G₂ α : Type}

def queries (index : κ → ι) (message : N → M) :
    QueryImpl (advSpec κ N G₁) (OracleComp (advSpec ι M G₁))
  | .inl (.inl n) => query (spec := advSpec ι M G₁) (.inl (.inl n))
  | .inl (.inr i) => query (spec := advSpec ι M G₁) (.inl (.inr (index i)))
  | .inr m => query (spec := advSpec ι M G₁) (.inr (message m))

def mapMain (index : κ → ι) (message : N → M)
    (oa : OracleComp (advSpec κ N G₁) (Output F N)) :
    OracleComp (advSpec ι M G₁) (Output F M) :=
  mapOutput message <$> simulateQ (queries index message) oa

def mapAdversary (index : κ → ι) (message : N → M)
    (A : Adversary F κ N G₁ G₂) : Adversary F ι M G₁ G₂ :=
  ⟨fun pk => mapMain index message (A.main pk)⟩

theorem mapMain_query_bind (index : κ → ι) (message : N → M)
    (q : (advSpec κ N G₁).Domain)
    (next : (advSpec κ N G₁).Range q → OracleComp (advSpec κ N G₁) (Output F N)) :
    mapMain index message (show OracleComp (advSpec κ N G₁) (Output F N) from query q >>= next) =
      (queries index message q >>= fun r => mapMain index message (next r) :
        OracleComp (advSpec ι M G₁) (Output F M)) := by
  simp only [mapMain, simulateQ_bind, simulateQ_HasQuery_query, map_bind]

def mapTranscript (index : κ → ι) (message : N → M) (tr : Transcript κ N G₁) :
    Transcript ι M G₁ := (tr.1.map (Prod.map index id), tr.2.map (Prod.map message id))

@[simp] theorem mapTranscript_empty (index : κ → ι) (message : N → M) :
    mapTranscript (G₁ := G₁) index message ([], []) = ([], []) := rfl

@[simp] theorem mapTranscript_hash (index : κ → ι) (message : N → M)
    (tr : Transcript κ N G₁) (i : κ) (r : G₁) :
    mapTranscript index message (tr.1 ++ [(i, r)], tr.2) =
      ((mapTranscript index message tr).1 ++ [(index i, r)],
        (mapTranscript index message tr).2) := by simp [mapTranscript]

@[simp] theorem mapTranscript_sign (index : κ → ι) (message : N → M)
    (tr : Transcript κ N G₁) (m : N) (r : G₁) :
    mapTranscript index message (tr.1, tr.2 ++ [(m, r)]) =
      ((mapTranscript index message tr).1,
        (mapTranscript index message tr).2 ++ [(message m, r)]) := by simp [mapTranscript]

section Execution

variable [AddCommMonoid R] [SMul F R]

theorem privateOracle_random (terms : M → List (ι × F)) (hash sign : R → G₁)
    (n : Nat) (tr : Transcript ι M G₁) :
    ((privateOracle terms hash sign) (.inl (.inl n))).run tr =
      (fun r => (r, tr)) <$>
        (liftM ((baseSpec ι R).query (.inl n)) : OracleComp (baseSpec ι R) (Fin (n + 1))) := by
  simp [privateOracle, handler]

theorem privateOracle_hash (terms : M → List (ι × F)) (hash sign : R → G₁)
    (i : ι) (tr : Transcript ι M G₁) :
    ((privateOracle terms hash sign) (.inl (.inr i))).run tr =
      (fun r => (hash r, (tr.1 ++ [(i, hash r)], tr.2))) <$>
        (liftM ((baseSpec ι R).query (.inr i)) : OracleComp (baseSpec ι R) R) := by
  simp [privateOracle, handler]

theorem privateOracle_sign (terms : M → List (ι × F)) (hash sign : R → G₁)
    (m : M) (tr : Transcript ι M G₁) :
    ((privateOracle terms hash sign) (.inr m)).run tr =
      (fun r => (sign r, (tr.1, tr.2 ++ [(m, sign r)]))) <$> evalTerms (terms m) := by
  simp [privateOracle, handler]

theorem privateSim_map (index : κ → ι) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (hash sign : R → G₁) (oa : OracleComp (advSpec κ N G₁) α) (tr : Transcript κ N G₁) :
    (simulateQ (privateOracle terms hash sign) (simulateQ (queries index message) oa)).run
        (mapTranscript index message tr) =
      Prod.map id (mapTranscript index message) <$>
        simulateQ (baseQueries index) ((simulateQ (privateOracle smallTerms hash sign) oa).run tr) := by
  induction oa using OracleComp.inductionOn generalizing tr with
  | pure a => simp
  | query_bind q next ih =>
    rcases q with ((n | i) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, queries,
        simulateQ_HasQuery_query, StateT.run_bind, privateOracle_random,
        privateOracle_hash, privateOracle_sign, ht, evalTerms_map,
        bind_map_left, baseQueries, map_bind]
    · exact bind_congr fun r => ih r tr
    · exact bind_congr fun r => by
        simpa only [mapTranscript_hash] using ih (hash r) (tr.1 ++ [(i, hash r)], tr.2)
    · exact bind_congr fun r => by
        simpa only [mapTranscript_sign] using ih (sign r) (tr.1, tr.2 ++ [(m, sign r)])

theorem privateRun_map (index : κ → ι) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (hash sign : R → G₁) (A : Adversary F κ N G₁ G₂) (pk : G₂) :
    privateRun terms hash sign (mapAdversary index message A) pk =
      Prod.map (mapOutput message) (mapTranscript index message) <$>
        simulateQ (baseQueries index) (privateRun smallTerms hash sign A pk) := by
  unfold privateRun mapAdversary mapMain
  simp only [simulateQ_map, StateT.run_map]
  rw [← mapTranscript_empty index message, privateSim_map index message terms smallTerms ht]
  simp only [Functor.map_map]
  congr 1

end Execution

theorem signedTerms_map [MulZeroOneClass F] (index : κ → ι) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (coeff : List F) (tr : List (N × G₁)) :
    signedTerms terms coeff (tr.map (Prod.map message id)) =
      (signedTerms smallTerms coeff tr).map (Prod.map index id) := by
  simp [signedTerms, List.mapIdx_eq_ofFn, List.map_ofFn, List.map_flatten,
    List.map_map, ht, Function.comp_def]

variable [Field F] [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_map (index : κ → ι) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (g X : G₁) (pk : G₂) (A : Adversary F κ N G₁ G₂) :
    goodProgram terms g X pk (mapAdversary index message A) =
      simulateQ (baseQueries index) (goodProgram smallTerms g X pk A) := by
  simp [goodProgram, privateRun_map index message terms smallTerms ht, mapOutput, mapTranscript,
    traceTerms_map, signedTerms_map index message terms smallTerms ht, ht, evalTerms_map, bind_map_left]

theorem badProgram_map (index : κ → ι) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F κ N G₁ G₂) :
    badProgram terms g X pk kappa (mapAdversary index message A) =
      simulateQ (baseQueries index) (badProgram smallTerms g X pk kappa A) := by
  simp [badProgram, privateRun_map index message terms smallTerms ht, mapOutput, mapTranscript,
    signedTerms_map index message terms smallTerms ht, ht, evalTerms_map, bind_map_left]

variable [SampleableType F] [DecidableEq κ] [DecidableEq ι]

theorem goodReduction_map (index : κ → ι) (hi : Function.Injective index) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (A : Adversary F κ N G₁ G₂) :
    goodReductionList terms (mapAdversary index message A) = goodReductionList smallTerms A := by
  rw [goodReductionList_eq, goodReductionList_eq]
  funext g X g₂ pk
  unfold goodReductionLazy
  rw [goodProgram_map index message terms smallTerms ht, lazyRun_rename index hi]

variable [AddCommGroup G₂] [Module F G₂]

theorem badReduction_map (index : κ → ι) (hi : Function.Injective index) (message : N → M)
    (terms : M → List (ι × F)) (smallTerms : N → List (κ × F))
    (ht : ∀ m, terms (message m) = (smallTerms m).map (Prod.map index id))
    (A : Adversary F κ N G₁ G₂) :
    badReductionList terms (mapAdversary index message A) = badReductionList smallTerms A := by
  rw [badReductionList_eq, badReductionList_eq]
  funext g X g₂ pk
  unfold badReductionLazy
  apply bind_congr
  intro kappa
  rw [badProgram_map index message terms smallTerms ht, lazyRun_rename index hi]

end Model.LazyAGM.WeightedTransport
