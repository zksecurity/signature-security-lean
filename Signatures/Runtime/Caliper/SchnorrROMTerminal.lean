import Signatures.Runtime.Caliper.SchnorrROMForgeryHashBounds

/-! A caller's returned forgery receives its final LIVE challenge. A pending
packet is a distinct cutoff and retains the private store without hashing.
Union padding and store movement are handled by executed copies. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
open Caliper BoundedSource ByteRoute SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G P : Type} (config : Signing.Enumerated.Configuration w M F G) (pending : Representation w P)

def width := 1 + (ForgeryHash.forgery config).representation.encoding.words + pending.encoding.words + config.handler.store.representation.encoding.words
variable (room : 8 * width config pending < 2 ^ w)
theorem fits (room : 8 * width config pending < 2 ^ w) {words : Nat}
    (bound : words ≤ 8 * width config pending) : words < 2 ^ w := bound.trans_lt room
abbrev Input := ((ForgeryHash.forgery config).Value ⊕ P) × config.handler.store.Value
abbrev Output := (Unit ⊕ ((ForgeryHash.forgery config).Value × config.handler.sampler.tape.scalar.Value)) × config.handler.store.Value
def input : Representation w (Input config (P := P)) := SumContext.input (ForgeryHash.forgery config).representation pending
  config.handler.store.representation config.sampler.wordFits (fits config pending room (by unfold width; omega))
def cutoffInput := pending.prod config.handler.store.representation (fits config pending room (by unfold width; omega))
def reply := (Pairing.unitRepresentation w).sum (ForgeryHash.result config) (width_pos config.sampler.wordFits)
  (fits config pending room (by change 1 + max 0 (_ + 1) ≤ _; unfold width; omega))
def output : Representation w (Output config) := (reply config pending room).prod config.handler.store.representation
  (fits config pending room (by change (1 + max 0 (_ + 1)) + _ ≤ _; unfold width; omega))
def distribute := SumContext.distribute (ForgeryHash.forgery config).representation pending
  config.handler.store.representation config.sampler.wordFits (input config pending room).fits
def successTag : Realizer .unit (ForgeryHash.output config) (output config pending room)
    (fun value => (.inr value.1, value.2)) :=
  SumContext.mergeRight (Pairing.unitRepresentation w) (ForgeryHash.result config) config.handler.store.representation
    config.sampler.wordFits (output config pending room).fits
def cutoffValue (value : P × config.handler.store.Value) : Output config := (.inl (), value.2)
def cutoffParts : List (Part w) :=
  [.literal (List.replicate (1 + (ForgeryHash.result config).encoding.words) 0),
   .slice pending.encoding.words config.handler.store.representation.encoding.words]
theorem cutoff_valid : Valid (cutoffInput config pending room).encoding.words (cutoffParts config pending) :=
  ⟨le_rfl, trivial⟩
theorem cutoff_size : words (cutoffParts config pending) = (output config pending room).encoding.words := by
  simp only [cutoffParts, words, List.length_replicate]
  change (1 + _) + (_ + 0) = (1 + max 0 _) + _
  omega
theorem cutoff_bytes (value : P × config.handler.store.Value) :
    bytes ((cutoffInput config pending room).encoding.encode value) (cutoffParts config pending) =
      (output config pending room).encoding.encode (cutoffValue config value) := by
  have block := slice_block (pending.encoding.encode value.1) (config.handler.store.representation.encoding.encode value.2) []
  simp only [List.append_nil, pending.encoding.encode_length, config.handler.store.representation.encoding.encode_length] at block
  change List.replicate (1 + (ForgeryHash.result config).encoding.words) 0 ++
    (((pending.encoding.encode value.1 ++ config.handler.store.representation.encoding.encode value.2).drop pending.encoding.words).take
      config.handler.store.representation.encoding.words ++ []) = _
  rw [block, List.append_nil]
  change List.replicate (1 + _) 0 ++ _ = (0 :: ([] ++ List.replicate (max 0 _ - 0) 0)) ++ _
  simp only [Nat.zero_max, Nat.sub_zero, List.nil_append, Nat.add_comm 1, List.replicate_succ, cutoffValue]
def cutoff : Realizer .unit (cutoffInput config pending room) (output config pending room) (cutoffValue config) :=
  ByteRoute.realizer _ _ _ (cutoffParts config pending) config.sampler.wordFits
    (cutoff_valid config pending room) (cutoff_size config pending room) (cutoff_bytes config pending room)

variable [Zero F] [DecidableEq M] [DecidableEq G]
def successCode : Interactive.Code w := .seq (ForgeryHash.code config) (.compute (successTag config pending room).code)
def code : Interactive.Code w := .seq (.compute (distribute config pending room).code)
  (Interactive.dispatch (successCode config pending room) (.compute (cutoff config pending room).code)
    (ForgeryHash.input config).encoding.words (cutoffInput config pending room).encoding.words)
def ready (value : Input config (P := P)) : Prop :=
  match value.1 with | .inl forge => ForgeryHash.ready config (forge, value.2) | .inr _ => True
def successSource (value : ForgeryHash.Input config) : ProbComp (Output config) :=
  (fun hashed => (.inr hashed.1, hashed.2)) <$> ForgeryHash.source config value
def source (value : Input config (P := P)) : ProbComp (Output config) :=
  match value.1 with | .inl forge => successSource config (forge, value.2) | .inr _ => pure (.inl (), value.2)

theorem success_refines : Interactive.RefinesOn (ForgeryHash.ready config) (Fresh.port config.handler.sampler.tape) .unit
    (ForgeryHash.input config) (output config pending room) (successSource config) (successCode config pending room) := by
  have refined := (ForgeryHash.refines config).seq
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (successTag config pending room)).on (fun _ => True))
    (fun _ _ _ _ => trivial)
  unfold successSource successCode
  simpa only [bind_pure_comp] using refined

theorem refines : Interactive.RefinesOn (ready config) (Fresh.port config.handler.sampler.tape) .unit
    (input config pending room) (output config pending room) (source config) (code config pending room) := by
  have branches := Interactive.RefinesOn.dispatch (ForgeryHash.input config) (cutoffInput config pending room) (output config pending room)
    (success_refines config pending room)
    ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit (cutoff config pending room)).on (fun _ => True))
    (width_pos config.sampler.wordFits)
    (SumContext.output (ForgeryHash.forgery config).representation pending config.handler.store.representation
      config.sampler.wordFits (input config pending room).fits).fits
  have compiled := ((Interactive.Refines.compute (Fresh.port config.handler.sampler.tape) .unit
    (distribute config pending room)).on (ready config)).seq branches (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      rcases value with ⟨forge | next, saved⟩ <;> exact valid)
  convert compiled using 1
  · rfl
  · funext value
    rcases value with ⟨forge | next, saved⟩ <;> simp only [source, pure_bind, SumContext.view] <;> rfl
  · rfl

theorem reserved_ready (value : Input config (P := P)) (reserved : Handler.Reserved config 0 value.2.val) : ready config value := by
  rcases value with ⟨forge | next, saved⟩
  · exact ForgeryHash.reserved_ready config (forge, saved) reserved
  · trivial

end Signatures.Runtime.CaliperBackend.SchnorrROM.Terminal
