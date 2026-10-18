import Signatures.Runtime.Caliper.BLSDispatchMemory
import Signatures.Runtime.Caliper.BLSReplyReachability

/-! Stored-tag dispatch preserves the original joint reply distribution. The
reservation theorem links supported machine returns to the next source state;
it does not assume a finished reply implementation or per-call capacity proof. -/

namespace Signatures.Runtime.CaliperBackend.BLSDispatch
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {C G : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)
    (drawSource : ProbComp layout.cache.value.Value)
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation
      (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawLaw in
theorem denote_source (signing : Bool) (value : (layout.input default.val signing).Value) :
    Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve drawSource (request layout default signing value) =
      (fun out => (out.1, value.val.2.1, out.2)) <$>
        (LazyAGM.listReply signing (fun sample => respond signing (sample, value.val.2.1)) value.val.1).run value.val.2.2 := by
  rw [denote_request]
  exact BLSReply.denote_source layout default signing P comparison correct (response signing) (responseBuffers signing) reserve drawSource drawLaw value

include drawCorrect drawLaw in
theorem observe (signing : Bool) (value : (layout.input default.val signing).Value)
    (tape : RandomTape w) (before : State w)
    (holds : (input layout default).representation.Holds (request layout default signing value) before) :
    (fun result => Subtype.val <$> Interactive.observe layout.output.representation result) <$>
      (code layout default P comparison correct port draw response responseBuffers reserve).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun sample => respond signing (sample, value.val.2.1)) value.val.1).run value.val.2.2) := by
  have observed := (refines layout default P comparison correct port draw response responseBuffers reserve
    drawSource drawCorrect).observe tape (request layout default signing value) before holds
  have mapped := congrArg (fun computation : ProbComp (Option layout.output.Value) =>
    (fun result => Subtype.val <$> result) <$> computation) observed
  rw [← denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw signing value]
  have middle : (fun result => Subtype.val <$> result) <$> some <$>
      denote layout default P comparison correct response responseBuffers reserve drawSource (request layout default signing value) =
        some <$> Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve drawSource (request layout default signing value) :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

include drawCorrect drawLaw in
/-- A supported dispatcher return is a supported original reply with its full
updated store still in memory and capacity reserved for the remaining calls. -/
theorem returns_reserved {remaining : Nat} {cfg : C}
    {state : LazyAGM.State (key.Value base) (val.Value base) G}
    (reserved : BLSReply.Reserved layout (remaining + 1) (cfg, state))
    (signing : Bool) (message : key.Value base) (messageFits : layout.cache.key.valid message)
    (tape : RandomTape w) (before : State w)
    (holds : (input layout default).representation.Holds
      (request layout default signing ⟨(message, cfg, state), reserved.ready default signing message messageFits⟩) before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout default P comparison correct port draw response responseBuffers reserve).execute port .unit tape before)) :
    ∃ answer ∈ support ((LazyAGM.listReply signing (fun sample => respond signing (sample, cfg)) message).run state),
      ∃ represented : layout.output.Value,
        represented.val = (answer.1, cfg, answer.2) ∧
        layout.output.representation.Holds represented finished.state ∧
        BLSReply.Reserved layout remaining (cfg, answer.2) := by
  let value : (layout.input default.val signing).Value := ⟨(message, cfg, state), reserved.ready default signing message messageFits⟩
  obtain ⟨represented, supported, result, equal, output, _, _⟩ :=
    (refines layout default P comparison correct port draw response responseBuffers reserve drawSource drawCorrect
      tape (request layout default signing value) before holds).right_support reached
  cases Option.some.inj equal
  have mapped : represented.val ∈ support
      (Subtype.val <$> denote layout default P comparison correct response responseBuffers reserve drawSource (request layout default signing value)) := by
    simp only [support_map, Set.mem_image]
    exact ⟨represented, supported, rfl⟩
  rw [denote_source layout default P comparison correct response responseBuffers reserve drawSource drawLaw signing value] at mapped
  simp only [support_map, Set.mem_image] at mapped
  obtain ⟨answer, sourceSupported, equal⟩ := mapped
  exact ⟨answer, sourceSupported, represented, equal.symm, output,
    BLSReply.reply_reserved layout default P comparison correct response responseBuffers reserve drawSource drawLaw
      reserved signing message messageFits answer sourceSupported⟩

end Signatures.Runtime.CaliperBackend.BLSDispatch
