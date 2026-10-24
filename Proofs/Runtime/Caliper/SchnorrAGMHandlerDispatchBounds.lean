import Proofs.Runtime.Caliper.SchnorrAGMHandlerDispatch

/-! Complete dispatch costs include both stored group branches, both tag levels,
request copying and saved-buffer retention. Only the selected branch runs. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound)

theorem packet_widths : (groupInput layout).encoding.words ≤ 5 * layout.width ∧
    (randomPacket layout).encoding.words ≤ 4 * layout.width ∧ (groupPacket layout).encoding.words ≤ 4 * layout.width ∧
    (groupOutput layout).encoding.words ≤ 5 * layout.width ∧ (output layout).encoding.words ≤ 6 * layout.width := by
  have := input_widths layout; have := layout.args_le; have := random_output_le layout
  have := layout.scalarOutput_le; have := layout.width_pos
  change (1 + max _ _ ≤ _) ∧ (_ + _ ≤ _) ∧ (_ + _ ≤ _) ∧
    (1 + max (_ + _) (_ + _) ≤ _) ∧ (1 + max (_ + _) (1 + max (_ + _) (_ + _)) ≤ _)
  omega

def timeBudget (hashTime signingTime : Nat) : Nat :=
  max (RandomComponent.timeBudget layout) (max hashTime signingTime) + 400 * layout.width + 10
def codeBudget (hashWords signingWords : Nat) : Nat :=
  RandomComponent.codeBudget layout + hashWords + signingWords + 3000 * layout.width + 400

omit [DecidableEq M] [DecidableEq G] in
theorem hashTag_time (value : layout.scalarOutput.Value × layout.groupArgs.Value) :
    (hashTag layout).time value ≤ 8 * (groupOutput layout).encoding.words + 8 * (output layout).encoding.words := by
  have first := inl_time (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits value
  have second := inr_time (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits (.inl value)
  exact Nat.add_le_add first second
omit [DecidableEq M] [DecidableEq G] in
theorem signingTag_time (value : layout.scalarOutput.Value × layout.groupArgs.Value) :
    (signingTag layout).time value ≤ 8 * (groupOutput layout).encoding.words + 8 * (output layout).encoding.words := by
  have first := inr_time (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits value
  have second := inr_time (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits (.inr value)
  exact Nat.add_le_add first second

theorem time_bound {hashBody signingBody : Interactive.Code w}
    {hash : layout.hashInput.Value → ProbComp layout.scalarOutput.Value}
    {signing : layout.signingInput.Value → ProbComp layout.scalarOutput.Value} {hashTime signingTime : Nat}
    (hashCorrect : Interactive.Refines layout.random.port .unit layout.hashInput.representation layout.scalarOutput.representation hash hashBody)
    (signingCorrect : Interactive.Refines layout.random.port .unit layout.signingInput.representation layout.scalarOutput.representation signing signingBody)
    (hashBound : Interactive.TimeBound layout.random.port .unit layout.hashInput.representation hashBody hashTime)
    (signingBound : Interactive.TimeBound layout.random.port .unit layout.signingInput.representation signingBody signingTime) :
    Interactive.TimeBound layout.random.port .unit (input layout) (code layout hashBody signingBody) (timeBudget layout hashTime signingTime) := by
  have random := (Interactive.Prefix.time_bound _ _ _ (random_prefix layout) _ _ _ _
    (RandomComponent.refines layout) (RandomComponent.time_bound layout)).seq (random_held_refines layout)
      (Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit) (randomTag layout) _ (inl_time _ _ _ _))
  have hashed := (Interactive.Prefix.time_bound _ _ _ (hash_prefix layout) _ _ _ _ hashCorrect hashBound).seq
    (hash_held_refines layout hashCorrect)
      (Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit) (hashTag layout) _ (hashTag_time layout))
  have signed := (Interactive.Prefix.time_bound _ _ _ (signing_prefix layout) _ _ _ _ signingCorrect signingBound).seq
    (signing_held_refines layout signingCorrect)
      (Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit) (signingTag layout) _ (signingTag_time layout))
  have group := Interactive.TimeBound.dispatch _ _ hashed signed (width_pos layout.scheme.wordFits) (groupInput layout).fits
  have combined := Interactive.TimeBound.dispatch _ _ random group (width_pos layout.scheme.wordFits) (input layout).fits
  apply combined.mono
  simp only [Interactive.dispatchTime_unit]
  have := input_widths layout; have := packet_widths layout; have := layout.args_le
  have := random_output_le layout; have := layout.scalarOutput_le
  change 2 + max (8 * _ + (_ + 8 * (output layout).encoding.words)) (8 * _ + (2 + max _ _)) ≤ _
  unfold timeBudget
  dsimp only [groupInput] at *
  omega

omit [DecidableEq M] [DecidableEq G] in
theorem hashTag_words : descriptionWords (hashTag layout).code ≤
    26 * (groupOutput layout).encoding.words + 26 * (output layout).encoding.words + 29 := by
  have first := inl_words (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits
  have second := inr_words (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits
  change descriptionWords _ ≤ 26 * (groupOutput layout).encoding.words + 14 at first
  change descriptionWords _ ≤ 26 * (output layout).encoding.words + 14 at second
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  omega
omit [DecidableEq M] [DecidableEq G] in
theorem signingTag_words : descriptionWords (signingTag layout).code ≤
    26 * (groupOutput layout).encoding.words + 26 * (output layout).encoding.words + 29 := by
  have first := inr_words (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits
  have second := inr_words (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits
  change descriptionWords _ ≤ 26 * (groupOutput layout).encoding.words + 14 at first
  change descriptionWords _ ≤ 26 * (output layout).encoding.words + 14 at second
  change descriptionWords (_ ;; _) ≤ _
  rw [descriptionWords_seq]
  omega

private theorem seq_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (body : Interactive.Code w) (tag : Stmt w) :
    ((body.seq (.compute tag)).lower port).descriptionWords = (body.lower port).descriptionWords + descriptionWords tag + 2 := by
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

theorem code_bound (hashBody signingBody : Interactive.Code w) {hashWords signingWords : Nat}
    (hashBound : (hashBody.lower layout.random.port).descriptionWords ≤ hashWords)
    (signingBound : (signingBody.lower layout.random.port).descriptionWords ≤ signingWords) :
    ((code layout hashBody signingBody).lower layout.random.port).descriptionWords ≤ codeBudget layout hashWords signingWords := by
  have random := Interactive.Prefix.code_bound _ _ _ (random_prefix layout) layout.scheme.wordFits (random_input_fits layout) layout.randomOutput.representation layout.random.port _ (RandomComponent.code_bound layout)
  have hashed := Interactive.Prefix.code_bound _ _ _ (hash_prefix layout) layout.scheme.wordFits (hash_input_fits layout) layout.scalarOutput.representation layout.random.port _ hashBound
  have signed := Interactive.Prefix.code_bound _ _ _ (signing_prefix layout) layout.scheme.wordFits (signing_input_fits layout) layout.scalarOutput.representation layout.random.port _ signingBound
  have rt := inl_words (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits
  have ht := hashTag_words layout; have st := signingTag_words layout
  change ((randomHeld layout).lower layout.random.port).descriptionWords ≤ _ at random
  change ((hashHeld layout hashBody).lower layout.random.port).descriptionWords ≤ _ at hashed
  change ((signingHeld layout signingBody).lower layout.random.port).descriptionWords ≤ _ at signed
  change descriptionWords (randomTag layout).code ≤ 26 * (output layout).encoding.words + 14 at rt
  rw [code, Interactive.dispatch_descriptionWords, groupCode, Interactive.dispatch_descriptionWords]
  rw [randomCode, hashCode, signingCode, seq_words, seq_words, seq_words]
  have := input_widths layout; have := packet_widths layout; have := layout.args_le
  have := random_output_le layout; have := layout.scalarOutput_le
  unfold codeBudget
  omega

omit [DecidableEq M] [DecidableEq G] in
theorem tag_names : NamesBound (randomTag layout).code 3 ∧ NamesBound (hashTag layout).code 3 ∧ NamesBound (signingTag layout).code 3 := by
  have outerLeft := inl_names (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits
  have outerRight := inr_names (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits
  have innerLeft := inl_names (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits
  have innerRight := inr_names (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits
  refine ⟨outerLeft, ?_, ?_⟩
  · exact ⟨max_le innerLeft.registers outerRight.registers, max_le innerLeft.buffers outerRight.buffers⟩
  · exact ⟨max_le innerRight.registers outerRight.registers, max_le innerRight.buffers outerRight.buffers⟩

theorem names (hashBody signingBody : Interactive.Code w) {slots : Nat}
    (hashNames : WordIO.NamesAccounted (hashBody.lower layout.random.port) slots)
    (signingNames : WordIO.NamesAccounted (signingBody.lower layout.random.port) slots) :
    WordIO.NamesAccounted ((code layout hashBody signingBody).lower layout.random.port) (max 5 slots) := by
  have tags := tag_names layout
  have random := Interactive.Prefix.names _ _ _ (random_prefix layout) layout.scheme.wordFits (random_input_fits layout) layout.randomOutput.representation layout.random.port _ (RandomComponent.names layout)
  have hashed := Interactive.Prefix.names _ _ _ (hash_prefix layout) layout.scheme.wordFits (hash_input_fits layout) layout.scalarOutput.representation layout.random.port _ hashNames
  have signed := Interactive.Prefix.names _ _ _ (signing_prefix layout) layout.scheme.wordFits (signing_input_fits layout) layout.scalarOutput.representation layout.random.port _ signingNames
  apply @Interactive.dispatch_names w Nat unifSpec layout.random.port
    (randomCode layout) (groupCode layout hashBody signingBody) (max 5 slots)
  · exact (random.mono (Nat.le_max_left 5 slots)).seq
      (WordIO.NamesAccounted.compute (tags.1.accounted.mono (by omega)))
  · apply @Interactive.dispatch_names w Nat unifSpec layout.random.port
      (hashCode layout hashBody) (signingCode layout signingBody) (max 5 slots)
    · exact (hashed.mono (Nat.le_max_right 5 slots)).seq
        (WordIO.NamesAccounted.compute (tags.2.1.accounted.mono (by omega)))
    · exact (signed.mono (Nat.le_max_right 5 slots)).seq
        (WordIO.NamesAccounted.compute (tags.2.2.accounted.mono (by omega)))

theorem descriptionFits (hashBody signingBody : Interactive.Code w)
    (hashFits : (hashBody.lower layout.random.port).DescriptionFits)
    (signingFits : (signingBody.lower layout.random.port).DescriptionFits)
    (hashReserve : Interactive.savedBuffer layout.random.port hashBody < 2 ^ w)
    (signingReserve : Interactive.savedBuffer layout.random.port signingBody < 2 ^ w) :
    ((code layout hashBody signingBody).lower layout.random.port).DescriptionFits := by
  have randomReserve : Interactive.savedBuffer layout.random.port (RandomComponent.code layout) < 2 ^ w := by
    have := RandomComponent.buffers layout; have := layout.scheme.wordFits
    unfold Interactive.savedBuffer; omega
  have random := Interactive.Prefix.descriptionFits _ _ _ (random_prefix layout) layout.scheme.wordFits (random_input_fits layout) layout.randomOutput.representation (randomPacket layout).fits layout.random.port _
    (RandomComponent.descriptionFits layout) randomReserve
  have hashed := Interactive.Prefix.descriptionFits _ _ _ (hash_prefix layout) layout.scheme.wordFits (hash_input_fits layout) layout.scalarOutput.representation (groupPacket layout).fits layout.random.port _ hashFits hashReserve
  have signed := Interactive.Prefix.descriptionFits _ _ _ (signing_prefix layout) layout.scheme.wordFits (signing_input_fits layout) layout.scalarOutput.representation (groupPacket layout).fits layout.random.port _ signingFits signingReserve
  exact Interactive.dispatch_descriptionFits _ _ _ _ _ layout.scheme.wordFits
    (.seq layout.scheme.wordFits random (.compute (randomTag layout).description_fits))
    (Interactive.dispatch_descriptionFits _ _ _ _ _ layout.scheme.wordFits
      (.seq layout.scheme.wordFits hashed (.compute (hashTag layout).description_fits))
      (.seq layout.scheme.wordFits signed (.compute (signingTag layout).description_fits))
      layout.hashInput.representation.fits layout.signingInput.representation.fits)
    layout.randomInput.representation.fits (groupInput layout).fits

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch
