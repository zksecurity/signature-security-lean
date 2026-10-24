import Proofs.Runtime.Caliper.SchnorrAGMLayout
import Proofs.Runtime.SchnorrAGMGrowth

/-! Reachable-state invariants for the bounded Schnorr AGM store. Every adaptive
reply branch is covered, including malformed requests and signing collisions.
Only encountered messages need to belong to their layout; the mathematical
message type can be infinite. These are source invariants for the forthcoming
Caliper handler refinement, not an assumption of its completed implementation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM
open OracleComp OracleSpec AlgebraicGroupModel.Interaction
open Signatures.Runtime.SchnorrAGM
open _root_.Schnorr.AGM
variable {F G M : Type} [Field F]

def MessagesValid (valid : M → Prop) (s : Signatures.Runtime.SchnorrAGM.State F G M) : Prop :=
  (∀ item ∈ s.cache, valid item.1.1) ∧ ∀ message ∈ s.signed, valid message

def requestValid (valid : M → Prop) (q : Explained F (Request M) (Group G)) : Prop :=
  match q.value.data with
  | .random _ => True
  | .hash message | .sign message => valid message

variable (valid : M → Prop)
theorem messages_initial : MessagesValid valid ({} : Signatures.Runtime.SchnorrAGM.State F G M) :=
  ⟨by simp, by simp⟩

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]

omit [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M] in
theorem messages_record (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (key : M × G) (affine : Affine F) (challenge : F)
    (stored : MessagesValid valid s) (admitted : valid key.1) :
    MessagesValid valid (record s key affine challenge) := by
  refine ⟨?_, stored.2⟩
  intro item member
  rcases List.mem_cons.mp member with rfl | previous
  · exact admitted
  · exact stored.1 item previous

omit [DecidableEq F] in
theorem messages_signed (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (g pk : G) (message : M) (challenge response : F)
    (stored : MessagesValid valid s) (admitted : valid message) :
    MessagesValid valid (signedState s g pk message challenge response) := by
  constructor
  · intro item member
    change item ∈ (match cacheMap s.cache (message, response • g - challenge • pk) with
      | some _ => s.cache
      | none => ((message, response • g - challenge • pk), ⟨challenge, none⟩) :: s.cache) at member
    split at member
    · exact stored.1 item member
    · rcases List.mem_cons.mp member with rfl | previous
      · exact admitted
      · exact stored.1 item previous
  · intro item member
    rcases List.mem_append.mp member with previous | appended
    · exact stored.2 item previous
    · exact (List.mem_singleton.mp appended) ▸ admitted

variable [SampleableType F]
omit [AddCommGroup G] [Module F G] in
theorem messages_read (key : M × G) (affine : Affine F)
    (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (stored : MessagesValid valid s) (admitted : valid key.1)
    (p : F × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((Signatures.Runtime.SchnorrAGM.read key affine).run s)) : MessagesValid valid p.2 := by
  cases lookup : cacheMap s.cache key with
  | some entry =>
      have equal : p = (entry.challenge, s) := by simpa [Signatures.Runtime.SchnorrAGM.read, StateT.run, lookup] using reached
      subst p
      exact stored
  | none =>
      simp only [Signatures.Runtime.SchnorrAGM.read, StateT.run, lookup, bind_pure_comp, support_map, Set.mem_image] at reached
      obtain ⟨challenge, _, rfl⟩ := reached
      exact messages_record valid s key affine challenge stored admitted

theorem messages_handler (g pk : G) (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (stored : MessagesValid valid s) (q : Explained F (Request M) (Group G))
    (admitted : requestValid valid q)
    (p : Message (Reply F M q.value.data) (Group G) × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((Signatures.Runtime.SchnorrAGM.handler g pk q).run s)) : MessagesValid valid p.2 := by
  rcases q with ⟨⟨request, groups⟩, coefficients⟩
  cases request with
  | random n =>
      simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
      obtain ⟨answer, _, rfl⟩ := reached
      by_cases empty : groups () = [] <;> simpa only [empty, ite_true, ite_false, rejected, MessagesValid] using stored
  | hash message =>
      simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run] at reached
      split at reached
      · rename_i point row _ _
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
        obtain ⟨mid, supported, rfl⟩ := reached
        exact messages_read valid (message, point) (flatten row s.representations) s stored admitted mid supported
      · simp only [support_pure, Set.mem_singleton_iff] at reached
        cases reached
        exact stored
  | sign message =>
      by_cases empty : groups () = []
      · simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run, empty, ne_eq, not_true_eq_false, ite_false,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
        obtain ⟨challenge, _, response, _, rfl⟩ := reached
        exact messages_signed valid s g pk message challenge response stored admitted
      · simp only [Signatures.Runtime.SchnorrAGM.handler, StateT.run, empty, ne_eq, not_false_eq_true, ite_true,
          support_pure, Set.mem_singleton_iff] at reached
        cases reached
        exact stored

theorem messages_simulate {A : Type} (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M)) A)
    (admitted : AllQueriesSatisfy program (requestValid valid))
    (s : Signatures.Runtime.SchnorrAGM.State F G M) (stored : MessagesValid valid s)
    (p : A × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((simulateQ (Signatures.Runtime.SchnorrAGM.handler g pk) program).run s)) : MessagesValid valid p.2 := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure answer =>
      have equal : p = (answer, s) := by simpa using reached
      subst p
      exact stored
  | query_bind q next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at admitted
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨mid, supported, reached⟩ := reached
      exact ih mid.1 (admitted.2 mid.1) mid.2
        (messages_handler valid g pk s stored q admitted.1 mid supported) reached

theorem messages_finish (g pk : G) (out : Explained F (M × F) (Group G))
    (admitted : valid out.value.data.1) (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (stored : MessagesValid valid s) (p : (Bool × F) × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((finish g pk out).run s)) : MessagesValid valid p.2 := by
  simp only [finish] at reached
  split at reached
  · rename_i point row _ _
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨mid, supported, rfl⟩ := reached
    exact messages_read valid (out.value.data.1, point) (flatten row s.representations)
      s stored admitted mid supported
  · have equal : p = ((false, 0), s) := by simpa using reached
    subst p
    exact stored

namespace Layouts
variable {w qH qS : Nat} (layout : Layouts w M F G qH qS)

/-- Space for remaining caller queries and one final extraction read. -/
def Reserved (hashes signatures : Nat) (s : Signatures.Runtime.SchnorrAGM.State F G M) : Prop :=
  MessagesValid layout.message.valid s ∧
    s.cache.length + hashes + signatures + 1 ≤ qH + qS + 1 ∧
    s.representations.length + signatures ≤ qS + 2 ∧ s.signed.length + signatures ≤ qS

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] in
theorem initial_reserved : layout.Reserved qH qS {} :=
  ⟨messages_initial _, by simp, by change 2 + qS ≤ qS + 2; omega, by simp⟩

theorem simulate_reserved {A : Type} (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M)) A)
    (admitted : AllQueriesSatisfy program (requestValid layout.message.valid))
    (hashes signatures futureHashes futureSignatures : Nat)
    (hS : IsQueryBoundP program (fun q => Reduction.signRequest q = true) signatures)
    (hH : IsQueryBoundP program (fun q => Reduction.hashRequest q = true) hashes)
    (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (room : layout.Reserved (hashes + futureHashes) (signatures + futureSignatures) s)
    (p : A × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((simulateQ (Signatures.Runtime.SchnorrAGM.handler g pk) program).run s)) :
    layout.Reserved futureHashes futureSignatures p.2 := by
  obtain ⟨cache, basis, signed⟩ := simulate_growth g pk program signatures hashes hS hH s p reached
  exact ⟨messages_simulate layout.message.valid g pk program admitted s room.1 p reached,
    by have := room.2.1; omega, by have := room.2.2.1; omega, by have := room.2.2.2; omega⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F] in
theorem Reserved.encoded {hashes signatures : Nat} {s : Signatures.Runtime.SchnorrAGM.State F G M}
    (room : layout.Reserved hashes signatures s)
    (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value) :
    layout.state.valid (Native.encodeState s) :=
  layout.encoded_valid scalars points s
    (by have := room.2.1; omega) (by have := room.2.2.1; omega) (by have := room.2.2.2; omega) room.1.1 room.1.2

theorem finish_encoded (g pk : G) (out : Explained F (M × F) (Group G))
    (admitted : layout.message.valid out.value.data.1)
    (s : Signatures.Runtime.SchnorrAGM.State F G M) (room : layout.Reserved 0 0 s)
    (p : (Bool × F) × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support ((finish g pk out).run s))
    (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value) :
    layout.state.valid (Native.encodeState p.2) := by
  obtain ⟨cache, basis, signed⟩ := finish_growth g pk out s p reached
  have messages := messages_finish layout.message.valid g pk out admitted s room.1 p reached
  exact layout.encoded_valid scalars points p.2
    (by have := room.2.1; omega) (by rw [basis]; have := room.2.2.1; omega)
    (by rw [signed]; have := room.2.2.2; omega) messages.1 messages.2

/-- Every final state of the original adaptive reduction fits the chosen store.
No enumeration of the mathematical message or group domains is required. -/
theorem run_encoded (g pk : G) (adversary : Adversary F G M)
    (admitted : AllQueriesSatisfy (adversary.main (initial g pk)) (requestValid layout.message.valid))
    (outputs : ∀ out ∈ support (adversary.main (initial g pk)), layout.message.valid out.value.data.1)
    (hS : IsQueryBoundP (adversary.main (initial g pk)) (fun q => Reduction.signRequest q = true) qS)
    (hH : IsQueryBoundP (adversary.main (initial g pk)) (fun q => Reduction.hashRequest q = true) qH)
    (p : (Bool × F) × Signatures.Runtime.SchnorrAGM.State F G M)
    (reached : p ∈ support (Signatures.Runtime.SchnorrAGM.run g pk adversary))
    (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value) :
    layout.state.valid (Native.encodeState p.2) := by
  simp only [Signatures.Runtime.SchnorrAGM.run, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨mid, supported, reached⟩ := reached
  have room := layout.simulate_reserved g pk (adversary.main (initial g pk)) admitted qH qS 0 0 hS hH
    {} (by simpa only [Nat.add_zero] using layout.initial_reserved) mid supported
  have returned : mid.1 ∈ support (adversary.main (initial g pk)) := by
    apply support_simulateQ_run'_subset (Signatures.Runtime.SchnorrAGM.handler g pk) _ {}
    change mid.1 ∈ support (Prod.fst <$> (simulateQ (Signatures.Runtime.SchnorrAGM.handler g pk)
      (adversary.main (initial g pk))).run {})
    rw [support_map]
    exact ⟨mid, supported, rfl⟩
  exact layout.finish_encoded g pk mid.1 (outputs mid.1 returned) mid.2 room p reached scalars points

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM
