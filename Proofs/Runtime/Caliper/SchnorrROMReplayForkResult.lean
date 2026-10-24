import Proofs.Runtime.Caliper.SchnorrROMReplayChallengeChecked
import Proofs.Runtime.Caliper.SchnorrROMReplayFirstChoice

/-! A fork returns failure or the complete first and second terminal outputs.
Every returned tag, padding word and reordered pass result is written by code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G X : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Result := Unit ⊕ (Terminal.Output config × Terminal.Output config)
def pair := (ReplaySecond.first config).prod (ReplaySecond.first config)
  (ReplaySecond.combinedFits config (by omega))
def output := (Pairing.unitRepresentation w).sum (pair config) (width_pos config.sampler.wordFits)
  (ReplaySecond.combinedFits config (by change 1 + max 0 (_ + _) ≤ _; omega))
def rejectParts : List (Part w) := [.literal ((output config).encoding.encode (.inl ()))]
theorem reject_size : ByteRoute.words (rejectParts config) = (output config).encoding.words := by
  change ((output config).encoding.encode (.inl ())).length + 0 = _
  rw [Encoding.encode_length, Nat.add_zero]
theorem reject_bytes (input : Representation w X) (value : X) :
    bytes (input.encoding.encode value) (rejectParts config) = (output config).encoding.encode (.inl ()) := by
  change _ ++ [] = _
  rw [List.append_nil]
def reject (input : Representation w X) : Realizer .unit input (output config) (fun _ => .inl ()) :=
  ByteRoute.realizer _ _ _ (rejectParts config) config.sampler.wordFits trivial (reject_size config) (reject_bytes config input)

def acceptParts : List (Part w) := [.literal [1],
  .slice ((ReplaySecond.first config).encoding.words + 2) (ReplaySecond.first config).encoding.words,
  .slice 0 (ReplaySecond.first config).encoding.words]
def acceptValue (value : ReplayMatch.Frame config) : Result config := .inr (value.2.2, value.1)
theorem accept_valid : Valid (ReplayMatch.frame config).encoding.words (acceptParts config) := by
  have size := ReplayMatch.frame_words config
  change (_ + 2 + _ ≤ _) ∧ (0 + _ ≤ _) ∧ True
  exact ⟨by omega, by omega, trivial⟩
theorem accept_size : ByteRoute.words (acceptParts config) = (output config).encoding.words := by
  change 1 + (_ + (_ + 0)) = 1 + max 0 (_ + _)
  omega
theorem accept_bytes (value : ReplayMatch.Frame config) :
    bytes ((ReplayMatch.frame config).encoding.encode value) (acceptParts config) = (output config).encoding.encode (acceptValue config value) := by
  let second := (ReplaySecond.first config).encoding.encode value.1
  let args := (ReplaySecond.arguments config).encoding.encode value.2.1
  let first := (ReplaySecond.first config).encoding.encode value.2.2
  have secondLength : second.length = (ReplaySecond.first config).encoding.words := Encoding.encode_length _ _
  have argsLength : args.length = 2 := Encoding.encode_length _ _
  have firstLength : first.length = (ReplaySecond.first config).encoding.words := Encoding.encode_length _ _
  have one := slice_block (second ++ args) first []
  have two := slice_block [] second (args ++ first)
  simp only [List.length_append, secondLength, argsLength, firstLength, List.length_nil, List.nil_append,
    List.append_nil, List.append_assoc] at one two
  change bytes (second ++ (args ++ first)) (acceptParts config) =
    1 :: ((pair config).encoding.encode (value.2.2, value.1) ++ List.replicate (max 0 (pair config).encoding.words - (pair config).encoding.words) 0)
  rw [Nat.zero_max, Nat.sub_self, List.replicate_zero, List.append_nil]
  change bytes (second ++ (args ++ first)) (acceptParts config) = 1 :: (first ++ second)
  simp only [acceptParts, bytes, List.append_nil]
  rw [one, two]
  rfl
def accept : Realizer .unit (ReplayMatch.frame config) (output config) (acceptValue config) :=
  ByteRoute.realizer _ _ _ (acceptParts config) config.sampler.wordFits (accept_valid config) (accept_size config) (accept_bytes config)

def matchChoice := (ReplayMatch.frame config).sum (ReplayMatch.frame config) (width_pos config.sampler.wordFits)
  (ReplaySecond.combinedFits config (by have := ReplayMatch.frame_words config; omega))
def chooseMatch (value : (Selection.boolean config).Value × ReplayMatch.Frame config) : ReplayMatch.Frame config ⊕ ReplayMatch.Frame config :=
  if value.1.val = true then .inr value.2 else .inl value.2
theorem chooseMatch_bytes (value : (Selection.boolean config).Value × ReplayMatch.Frame config) :
    (matchChoice config).encoding.encode (chooseMatch config value) = (ReplayMatch.output config).encoding.encode value := by
  rcases value with ⟨⟨flag, valid⟩, frame⟩
  cases flag
  all_goals
    simp only [chooseMatch, Bool.false_eq_true, ↓reduceIte]
    change _ :: (_ ++ List.replicate (_ - _) 0) = _
    rw [Nat.max_self, Nat.sub_self, List.replicate_zero, List.append_nil]
    rfl

def finishSource (value : (Selection.boolean config).Value × ReplayMatch.Frame config) : Result config :=
  if value.1.val = true then acceptValue config value.2 else .inl ()
def dispatched := branchRealizer .unit (by decide) (ReplayMatch.frame config) (ReplayMatch.frame config) (output config)
  (reject config (ReplayMatch.frame config)) (accept config) config.sampler.wordFits (matchChoice config).fits
def finish : Realizer .unit (ReplayMatch.output config) (output config) (finishSource config) :=
  ((dispatched config).viewInput (ReplayMatch.output config) (chooseMatch config) (fun value => (chooseMatch_bytes config value).symm)).viewOutput
    (output config) (finishSource config) (by intro value; rcases value with ⟨⟨flag, valid⟩, frame⟩; cases flag <;> rfl)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
