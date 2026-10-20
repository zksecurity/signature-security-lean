import Signatures.BLS.Statement
import Signatures.OOPS.Statement
import Signatures.Proximity.Statement
import Signatures.Model.Proofs.DirectAGM
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! A certified attacker constructed directly in the shared AGM interface.
Interleaved and repeated replies retain their chronological positions; malformed
protocol shapes are rejected even when their algebraic explanations are valid. -/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction
open Model.LazyAGM.Interactive

namespace SignaturesTest.DirectSharedAGM

private abbrev F := ZMod 101
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩
private abbrev G := Group F F
private abbrev spec := explainedSpec F G (Query Nat Nat) Reply

private def adaptive (count : Nat) (extraQueryGroup extraKeyOutput : Bool)
    (inputs : Groups G) : OracleComp spec (Explained F Nat G) := do
  let first ← spec.query (Explained.ofVectors inputs (.inl (.inr 4))
    (fun _ => if extraQueryGroup then [fun _ => 0] else []))
  let basis := extend inputs first.groups
  let signed ← spec.query (Explained.ofVectors basis (.inr 7) (fun _ => []))
  let basis := extend basis signed.groups
  let repeated ← spec.query (Explained.ofVectors basis (.inl (.inr 4)) (fun _ => []))
  let basis := extend basis repeated.groups
  return Explained.ofVectors basis 9 (fun sort => match sort with
    | .signature => List.replicate count (fun i => ([2, 3, 7, 5] : List F)[i.val]?.getD 0)
    | .verification => if extraKeyOutput then [fun _ => 1] else [])

private def attacker (count : Nat := 1) (extraQueryGroup : Bool := false)
    (extraKeyOutput : Bool := false) : Model.DirectAGM.Adversary F Nat Nat F F where
  main input := adaptive count extraQueryGroup extraKeyOutput input.groups
  algebraic input := by
    refine ⟨Explained.valid_ofVectors _ _ _, fun first => ?_⟩
    refine ⟨Explained.valid_ofVectors _ _ _, fun signed => ?_⟩
    refine ⟨Explained.valid_ofVectors _ _ _, fun repeated => ?_⟩
    exact Explained.valid_ofVectors _ _ _

private def execute (count : Nat := 1) (extraQueryGroup : Bool := false)
    (extraKeyOutput : Bool := false) :=
  ((attacker count extraQueryGroup extraKeyOutput).run
    (Model.DirectAGM.oracle (N := Id) (fun _ => pure ⟨0, Nat.zero_lt_succ _⟩)
      (fun i => pure (i : F)) (fun m => pure (2 * (m : F))))
    (initialInput (2 : F) (42 : F))).run {}

private def observed (count : Nat := 1) (extraQueryGroup : Bool := false)
    (extraKeyOutput : Bool := false) : Model.DirectAGM.Result F Nat F :=
  let outcome := execute count extraQueryGroup extraKeyOutput
  Model.DirectAGM.result outcome.1.1 outcome.2

-- The generator, two equal hash replies, and the intervening signature have
-- separate positions. The verification-group key is not in this basis.
example : (execute).1.2 .signature = [2, 4, 14, 4] := by decide
example : (execute).1.2 .verification = [42] := by decide
example : (execute).2.positions.hashes = [1, 3] := by decide
example : (execute).2.positions.signatures = [2] := by decide

example : (observed).signature = 33 ∧ (observed).message = 9 ∧
    (observed).signedMessages = [7] ∧ (observed).signingCoefficients = [7] ∧
    (observed).wellFormed = true := by decide

example : let output := Model.DirectAGM.grouped (execute).1.1 (execute).2.positions
    output.β = 2 ∧ output.γ = [3, 5] ∧ output.ξ = [7] := by decide

-- These are certified algebraic attackers, but not well-formed signature attempts.
example : (observed 0).wellFormed = false := by decide
example : (observed 2).wellFormed = false := by decide
example : (observed 1 true).wellFormed = false := by decide
example : (observed 1 false true).wellFormed = false := by decide

-- Public games accept the shared type without converting an old coefficient attacker.
example (curve : Model.PairingCurve) (n : Nat)
    {Message : Type}
    (A : Model.DirectAGM.Adversary (curve.Scalar n) Message Message
      (curve.SignatureGroup n) (curve.KeyGroup n)) :
    BLS.Game.AlgebraicAdversary curve n (Message := Message) := A

example (curve : Model.PairingCurve) (n degree : Nat) {Topic : Type}
    (A : Model.DirectAGM.Adversary (curve.Scalar n) (Topic × Fin (degree + 1))
      (curve.Scalar n × Topic) (curve.SignatureGroup n) (curve.KeyGroup n)) :
    OOPS.Game.AlgebraicAdversary curve n degree (Topic := Topic) := A

example (curve : Model.PairingCurve) (n dimension : Nat) {Slot : Type}
    (A : Model.DirectAGM.Adversary (curve.Scalar n) (Option (Fin dimension) × Slot)
      ((Fin dimension → curve.Scalar n) × Slot) (curve.SignatureGroup n) (curve.KeyGroup n)) :
    Proximity.Game.AlgebraicAdversary curve n dimension (Slot := Slot) := A

open Lean Meta in
run_meta do
  for name in #[``BLS.CaliperAGM.AlgebraicAdversary.source,
      ``Signatures.Runtime.WeightedCaliper.AlgebraicAdversary.source] do
    let type := (← getConstInfo name).type
    unless (type.find? fun e => e.isConstOf ``Model.DirectAGM.Adversary).isSome do
      throwError "{name}: the resource record must retain the shared source attacker"
  for name in #[``Model.DirectAGM.run_eq, ``Model.DirectAGM.game_le,
      ``Model.DirectAGM.ProofView.adversary_query_bound,
      ``Proximity.DirectAGM.collisionGame_eq,
      ``BLS.agm_security, ``OOPS.agm_security, ``Proximity.agm_security] do
    for axiomName in (← collectAxioms name) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.DirectSharedAGM
