import Proofs.Runtime.LazyAGMReply
import Proofs.BLS.LazyAGMList
import Proofs.BLS.LazyAGMTransport

/-! Flatten the lazy solver's private cache and transcript into one execution
state. This is a semantic bridge for general callers: it quantifies over every
adaptive oracle program, without requiring an arithmetic-source implementation.
The joint final cache, chronological transcript, and output are all preserved.
-/

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.Reduction

namespace Signatures.Runtime.LazyAGM

variable {F M R G₁ G₂ α : Type} [DecidableEq M] [SampleableType R]

abbrev State (M R G₁ : Type) := List (M × R) × Transcript M M G₁

def State.Messages (p : M → Prop) (state : State M R G₁) : Prop :=
  (∀ entry ∈ state.1, p entry.1) ∧
    (∀ entry ∈ state.2.1, p entry.1) ∧ (∀ entry ∈ state.2.2, p entry.1)

noncomputable def listReply (signing : Bool) (response : R → G₁) (m : M) :
    StateT (State M R G₁) ProbComp G₁ := fun state =>
  (fun p => let r := response p.1
    (r, p.2, record signing m r state.2)) <$>
      ((privateListOracle (M := M) (R := R)) (.inr m)).run state.1

noncomputable def listOracle (hash sign : R → G₁) :
    QueryImpl (advSpec M M G₁) (StateT (State M R G₁) ProbComp) := fun q => match q with
  | .inl (.inl n) => fun state =>
      (fun r => (r, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr m) => listReply false hash m
  | .inr m => listReply true sign m

theorem listOracle_random (hash sign : R → G₁) (n : Nat) (state : State M R G₁) :
    ((listOracle hash sign) (.inl (.inl n))).run state =
      (fun r => (r, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem listOracle_hash (hash sign : R → G₁) (m : M) (state : State M R G₁) :
    ((listOracle hash sign) (.inl (.inr m))).run state =
      (fun p => (hash p.1, p.2, record false m (hash p.1) state.2)) <$>
        ((privateListOracle (M := M) (R := R)) (.inr m)).run state.1 := rfl

theorem listOracle_sign (hash sign : R → G₁) (m : M) (state : State M R G₁) :
    ((listOracle hash sign) (.inr m)).run state =
      (fun p => (sign p.1, p.2, record true m (sign p.1) state.2)) <$>
        ((privateListOracle (M := M) (R := R)) (.inr m)).run state.1 := rfl

/-- Reverse only the explicit reply lists in this proof view. The private
cache order remains unchanged, including any shadowed initial entries. -/
def observe (p : α × State M R G₁) : (α × Transcript M M G₁) × List (M × R) :=
  ((p.1, chronological p.2.2), p.2.1)

theorem listSimulation (hash sign : R → G₁) (oa : OracleComp (advSpec M M G₁) α)
    (cache : List (M × R)) (tr : Transcript M M G₁) :
    observe <$> (simulateQ (listOracle hash sign) oa).run (cache, tr) =
      (simulateQ privateListOracle
        ((simulateQ (privateOracle hash sign) oa).run (chronological tr))).run cache := by
  induction oa using OracleComp.inductionOn generalizing cache tr with
  | pure a => simp [observe]
  | query_bind q next ih =>
    rcases q with ((n | m) | m) <;>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        BLS.LazyAGM.MessageTransport.privateOracle_random,
        BLS.LazyAGM.MessageTransport.privateOracle_hash,
        BLS.LazyAGM.MessageTransport.privateOracle_sign,
        listOracle_random, listOracle_hash, listOracle_sign, map_bind, bind_map_left,
        simulateQ_bind, simulateQ_spec_query]
    · exact bind_congr fun r => ih r cache tr
    · apply bind_congr
      intro p
      simpa only [chronological_record, Bool.false_eq_true, ite_false] using
        ih (hash p.1) p.2 (record false m (hash p.1) tr)
    · apply bind_congr
      intro p
      simpa only [chronological_record, ite_true] using
        ih (sign p.1) p.2 (record true m (sign p.1) tr)

theorem listRun (hash sign : R → G₁) (A : Adversary F M M G₁ G₂) (pk : G₂) :
    observe <$> (simulateQ (listOracle hash sign) (A.main pk)).run ([], ([], [])) =
      (simulateQ privateListOracle (privateRun hash sign A pk)).run [] := by
  simpa only [chronological, List.reverse_nil, privateRun] using
    listSimulation hash sign (A.main pk) [] ([], [])

theorem listReply_growth (signing : Bool) (response : R → G₁) (m : M)
    (state : State M R G₁) (out : G₁ × State M R G₁)
    (hout : out ∈ support ((listReply signing response m).run state)) :
    out.2.1.length ≤ state.1.length + 1 ∧
      out.2.2.1.length + out.2.2.2.length = state.2.1.length + state.2.2.length + 1 := by
  simp only [listReply, StateT.run, support_map, Set.mem_image] at hout
  obtain ⟨p, hp, rfl⟩ := hout
  have h := privateListOracle_growth (.inr m) state.1 p hp
  refine ⟨h, ?_⟩
  cases signing <;> simp [record] <;> omega

theorem listReply_messages (signing : Bool) (response : R → G₁) (m : M)
    (p : M → Prop) (state : State M R G₁) (hi : state.Messages p) (hm : p m)
    (out : G₁ × State M R G₁)
    (hout : out ∈ support ((listReply signing response m).run state)) :
    out.2.Messages p := by
  simp only [listReply, StateT.run, support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  have hc : ∀ entry ∈ r.2, p entry.1 := by
    change r ∈ support (((privateListOracle (M := M) (R := R)) (.inr m)).run state.1) at hr
    rw [privateListOracle_lookup] at hr
    split at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact hi.1
    · simp only [support_map, Set.mem_image] at hr
      obtain ⟨v, _, rfl⟩ := hr
      intro entry he
      rcases List.mem_cons.mp he with he | he
      · simpa only [he] using hm
      · exact hi.1 entry he
  refine ⟨hc, ?_⟩
  cases signing <;> simp only [record, Bool.false_eq_true, ite_false, ite_true]
  · refine ⟨?_, hi.2.2⟩
    intro entry he
    rcases List.mem_cons.mp he with he | he
    · simpa only [he] using hm
    · exact hi.2.1 entry he
  · refine ⟨hi.2.1, ?_⟩
    intro entry he
    rcases List.mem_cons.mp he with he | he
    · simpa only [he] using hm
    · exact hi.2.2 entry he

theorem listOracle_growth (hash sign : R → G₁) (q : (advSpec M M G₁).Domain)
    (state : State M R G₁) (out : (advSpec M M G₁).Range q × State M R G₁)
    (hout : out ∈ support (((listOracle hash sign) q).run state)) :
    out.2.1.length ≤ state.1.length + 1 ∧
      out.2.2.1.length + out.2.2.2.length ≤ state.2.1.length + state.2.2.length + 1 := by
  rcases q with ((n | m) | m)
  · rw [listOracle_random] at hout
    simp only [support_map, Set.mem_image] at hout
    obtain ⟨r, _, rfl⟩ := hout
    exact ⟨Nat.le_succ _, Nat.le_succ _⟩
  · have h := listReply_growth false hash m state out hout
    exact ⟨h.1, h.2.le⟩
  · have h := listReply_growth true sign m state out hout
    exact ⟨h.1, h.2.le⟩

theorem listSimulation_growth (hash sign : R → G₁) (oa : OracleComp (advSpec M M G₁) α)
    (state : State M R G₁) (q : Nat) (hq : IsTotalQueryBound oa q) (out : α × State M R G₁)
    (hout : out ∈ support ((simulateQ (listOracle hash sign) oa).run state)) :
    out.2.1.length ≤ state.1.length + q ∧
      out.2.2.1.length + out.2.2.2.length ≤ state.2.1.length + state.2.2.length + q := by
  induction oa using OracleComp.inductionOn generalizing q state with
  | pure a =>
    have he : out = (a, state) := by simpa using hout
    subst out
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hout
    obtain ⟨mid, hmid, hout⟩ := hout
    have hg := listOracle_growth hash sign query state mid hmid
    have ht := ih mid.1 mid.2 (q - 1) (hq.2 mid.1) hout
    constructor <;> omega

end Signatures.Runtime.LazyAGM
