import Signatures.Runtime.WeightedReply
import Signatures.LinearFunctional.Proofs.LazyAGMTransport
import Signatures.LinearFunctional.Proofs.LazyAGMCache

/-! Flatten the weighted source's nested cache/transcript simulation into one
private state. Equality retains the output, complete cache and chronological
reply logs for every adaptive caller, with no finite query-domain assumption. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

namespace Signatures.Runtime.WeightedAGM

open Reply

variable {F ι M R G₁ G₂ α : Type} [DecidableEq ι] [SampleableType R]
  [AddCommMonoid R] [SMul F R]

abbrev State (ι M R G₁ : Type) := List (ι × R) × Transcript ι M G₁

noncomputable def listReply (request : ι ⊕ M) (response : R → G₁)
    (action : OracleComp (baseSpec ι R) R) : StateT (State ι M R G₁) ProbComp G₁ := fun state =>
  (fun p => let r := response p.1
    (r, p.2, record request r state.2)) <$>
      (simulateQ privateListOracle action).run state.1

noncomputable def listOracle (terms : M → List (ι × F)) (hash sign : R → G₁) :
    QueryImpl (advSpec ι M G₁) (StateT (State ι M R G₁) ProbComp) := fun q => match q with
  | .inl (.inl n) => fun state =>
      (fun r => (r, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr i) => listReply (.inl i) hash (liftM ((baseSpec ι R).query (.inr i)))
  | .inr m => listReply (.inr m) sign (evalTerms (terms m))

theorem listOracle_random (terms : M → List (ι × F)) (hash sign : R → G₁)
    (n : Nat) (state : State ι M R G₁) :
    ((listOracle terms hash sign) (.inl (.inl n))).run state =
      (fun r => (r, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem listOracle_hash (terms : M → List (ι × F)) (hash sign : R → G₁)
    (i : ι) (state : State ι M R G₁) :
    ((listOracle terms hash sign) (.inl (.inr i))).run state =
      (fun p => (hash p.1, p.2, record (.inl i) (hash p.1) state.2)) <$>
        ((privateListOracle (M := ι) (R := R)) (.inr i)).run state.1 := by
  simp only [listOracle, listReply, StateT.run, simulateQ_spec_query]
  rfl

theorem listOracle_sign (terms : M → List (ι × F)) (hash sign : R → G₁)
    (m : M) (state : State ι M R G₁) :
    ((listOracle terms hash sign) (.inr m)).run state =
      (fun p => (sign p.1, p.2, record (.inr m) (sign p.1) state.2)) <$>
        (simulateQ (privateListOracle (M := ι) (R := R)) (evalTerms (terms m))).run state.1 := rfl

/-- Reverse the explicit reply lists only; preserve the exact cache list. -/
def observe (p : α × State ι M R G₁) : (α × Transcript ι M G₁) × List (ι × R) :=
  ((p.1, chronological p.2.2), p.2.1)

theorem listSimulation (terms : M → List (ι × F)) (hash sign : R → G₁)
    (oa : OracleComp (advSpec ι M G₁) α) (cache : List (ι × R)) (tr : Transcript ι M G₁) :
    observe <$> (simulateQ (listOracle terms hash sign) oa).run (cache, tr) =
      (simulateQ privateListOracle
        ((simulateQ (WeightedReduction.privateOracle terms hash sign) oa).run (chronological tr))).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache tr with
  | pure a => simp [observe]
  | query_bind q next ih =>
    rcases q with ((n | i) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        WeightedTransport.privateOracle_random, WeightedTransport.privateOracle_hash,
        WeightedTransport.privateOracle_sign, listOracle_random, listOracle_hash, listOracle_sign,
        map_bind, bind_map_left, simulateQ_bind, simulateQ_spec_query]
    · exact bind_congr fun r => ih r cache tr
    · apply bind_congr
      intro p
      simpa only [chronological_record] using
        ih (hash p.1) p.2 (record (.inl i) (hash p.1) tr)
    · apply bind_congr
      intro p
      simpa only [chronological_record] using
        ih (sign p.1) p.2 (record (.inr m) (sign p.1) tr)

theorem listRun (terms : M → List (ι × F)) (hash sign : R → G₁)
    (A : Adversary F ι M G₁ G₂) (pk : G₂) :
    observe <$> (simulateQ (listOracle terms hash sign) (A.main pk)).run ([], ([], [])) =
      (simulateQ privateListOracle (WeightedReduction.privateRun terms hash sign A pk)).run [] := by
  simpa only [chronological, List.reverse_nil, WeightedReduction.privateRun] using
    listSimulation terms hash sign (A.main pk) [] ([], [])

theorem listHash_growth (terms : M → List (ι × F)) (hash sign : R → G₁)
    (i : ι) (state : State ι M R G₁) (out : G₁ × State ι M R G₁)
    (hout : out ∈ support (((listOracle terms hash sign) (.inl (.inr i))).run state)) :
    out.2.1.length ≤ state.1.length + 1 ∧
      out.2.2.1.length = state.2.1.length + 1 ∧ out.2.2.2 = state.2.2 := by
  simp only [listOracle, listReply, StateT.run, simulateQ_spec_query, support_map, Set.mem_image] at hout
  obtain ⟨p, hp, rfl⟩ := hout
  have h := WeightedReduction.listLookup_preserves i state.1 p hp
  exact ⟨h.2.2, rfl, rfl⟩

theorem listSign_growth (terms : M → List (ι × F)) (hash sign : R → G₁)
    (m : M) (state : State ι M R G₁) (out : G₁ × State ι M R G₁)
    (hout : out ∈ support (((listOracle terms hash sign) (.inr m)).run state)) :
    out.2.1.length ≤ state.1.length + (terms m).length ∧
      out.2.2.1 = state.2.1 ∧ out.2.2.2.length = state.2.2.length + 1 := by
  simp only [listOracle, listReply, StateT.run, support_map, Set.mem_image] at hout
  obtain ⟨p, hp, rfl⟩ := hout
  have h := WeightedReduction.evalTerms_list_preserves (terms m) state.1 p hp
  exact ⟨h.2.2, rfl, rfl⟩

end Signatures.Runtime.WeightedAGM
