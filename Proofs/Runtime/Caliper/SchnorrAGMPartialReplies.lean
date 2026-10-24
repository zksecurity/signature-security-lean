import Proofs.Runtime.Caliper.SchnorrAGMCallerReplyEncoding

/-! Partial conversion preserves every represented canonical source reply.
Unrepresented replies have no local continuation in the constructed source. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G : Type}
    (layout : Handler.Layouts w M F G qH qS randomBound)

noncomputable def decodeReply (q : Request layout)
    (answer : (Interface.sourceSpec F G M).Range (query layout q)) : Option (Reply layout) := by
  classical
  exact if represented : ∃ value, replyMatches layout q value answer then some represented.choose else none

theorem decodeReply_eq_some (q : Request layout)
    (answer : (Interface.sourceSpec F G M).Range (query layout q)) (represented : Reply layout) :
    decodeReply layout q answer = some represented ↔ replyMatches layout q represented answer := by
  classical
  unfold decodeReply
  split
  · rename_i available
    constructor
    · intro equal
      obtain rfl := Option.some.inj equal
      exact available.choose_spec
    · intro related
      exact congrArg some (canonical_reply_injective layout available.choose_spec.2 related.2
        (available.choose_spec.1.trans related.1.symm))
  · rename_i missing
    constructor
    · intro equal
      cases equal
    · intro related
      exact (missing ⟨represented, related⟩).elim

theorem decodeReply_available [Zero F] (zeroValid : layout.scheme.scalar.valid (0 : F))
    (q : Request layout) : ∃ answer represented, decodeReply layout q answer = some represented := by
  obtain ⟨represented, related⟩ := defaultReply_represented layout zeroValid q
  exact ⟨_, represented, (decodeReply_eq_some layout q _ represented).mpr related⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
