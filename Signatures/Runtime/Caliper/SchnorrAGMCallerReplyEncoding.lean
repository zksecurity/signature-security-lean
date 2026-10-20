import Signatures.Runtime.Caliper.SchnorrAGMCallerInvariant

/-! Canonical replies determine the exact caller packet. In particular, random
answers are kept in range before `Fin` tagging, so modulo conversion cannot
identify different stored answers. Unrepresented source replies are totalized
only in the mathematical caller presentation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native

private def indexView {F G M : Type} : Interface.SourceIndex F G M →
    Interface.NativeRequest F G M × (Nat ⊕ F) × List G
  | ⟨⟨⟨.random n, groups⟩, rows⟩, answer⟩ =>
      (.inl (n, groups (), rows ()), .inl answer.data.val, answer.groups ())
  | ⟨⟨⟨.hash m, groups⟩, rows⟩, answer⟩ =>
      (.inr (.inl (m, groups (), rows ())), .inr answer.data, answer.groups ())
  | ⟨⟨⟨.sign m, groups⟩, rows⟩, answer⟩ =>
      (.inr (.inr (m, groups (), rows ())), .inr answer.data, answer.groups ())

variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

private def packetView : Reply layout → Interface.NativeRequest F G M × (Nat ⊕ F) × List G
  | .inl (answer, args) => (.inl args.val, .inl answer.val.1, answer.val.2)
  | .inr (.inl (answer, args)) => (.inr (.inl args.val), .inr answer.val.1, answer.val.2)
  | .inr (.inr (answer, args)) => (.inr (.inr args.val), .inr answer.val.1, answer.val.2)

private theorem packetView_injective : Function.Injective (packetView layout) := by
  intro lhs rhs equal
  rcases lhs with ⟨answer, args⟩ | ⟨answer, args⟩ | ⟨answer, args⟩ <;>
    rcases rhs with ⟨answer', args'⟩ | ⟨answer', args'⟩ | ⟨answer', args'⟩ <;>
    simp only [packetView, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and] at equal
  all_goals
    obtain ⟨argsEq, answerEq, groupsEq⟩ := equal
    have ha : answer = answer' := Subtype.ext (Prod.ext answerEq groupsEq)
    have hq : args = args' := Subtype.ext argsEq
    subst answer'
    subst args'
    rfl

private theorem indexView_replyValue (value : Reply layout) (canonical : canonicalReply layout value) :
    indexView (replyValue layout value) = packetView layout value := by
  rcases value with ⟨answer, args⟩ | ⟨answer, args⟩ | ⟨answer, args⟩
  · change ((Sum.inl args.val, Sum.inl (answer.val.1 % (args.val.1 + 1)), answer.val.2) :
        Interface.NativeRequest F G M × (Nat ⊕ F) × List G) = packetView layout (.inl (answer, args))
    rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le canonical)]
    rfl
  · rfl
  · rfl

theorem canonical_reply_injective {lhs rhs : Reply layout}
    (leftCanonical : canonicalReply layout lhs) (rightCanonical : canonicalReply layout rhs)
    (equal : replyValue layout lhs = replyValue layout rhs) : lhs = rhs := by
  apply packetView_injective layout
  rw [← indexView_replyValue layout lhs leftCanonical, ← indexView_replyValue layout rhs rightCanonical, equal]

variable [Zero F] (zeroValid : layout.scheme.scalar.valid (0 : F))

private def defaultPacket : Request layout → Reply layout
  | .inl args => .inl (⟨(0, []), Nat.succ_pos _, by exact ⟨by change 0 ≤ 1; decide, by simp⟩⟩, args)
  | .inr (.inl args) => .inr (.inl (⟨(0, []), zeroValid, by exact ⟨by change 0 ≤ 1; decide, by simp⟩⟩, args))
  | .inr (.inr args) => .inr (.inr (⟨(0, []), zeroValid, by exact ⟨by change 0 ≤ 1; decide, by simp⟩⟩, args))

/-- Select the unique represented canonical packet when one exists. The
fallback only extends the source to replies outside the represented interface;
it is never used by a related actual handler reply. -/
noncomputable def representReply (q : Request layout)
    (answer : (Interface.sourceSpec F G M).Range (query layout q)) : Reply layout := by
  classical
  exact if existsPacket : ∃ represented, replyMatches layout q represented answer
    then existsPacket.choose else defaultPacket layout zeroValid q

theorem representReply_eq (q : Request layout) (represented : Reply layout)
    (answer : (Interface.sourceSpec F G M).Range (query layout q))
    (related : replyMatches layout q represented answer) :
    represented = representReply layout zeroValid q answer := by
  classical
  have existsPacket : ∃ represented, replyMatches layout q represented answer := ⟨represented, related⟩
  rw [representReply, dite_eq_left existsPacket]
  exact canonical_reply_injective layout related.2 existsPacket.choose_spec.2
    (related.1.trans existsPacket.choose_spec.1.symm)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
