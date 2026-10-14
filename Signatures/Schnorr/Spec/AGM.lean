import AlgebraicGroupModel.Interaction
import Signatures.Schnorr.Spec.ROM

/-!
Schnorr's adaptive AGM interface. The commitment in a hash request is an
explained group argument, never ordinary data. A hash reply is a scalar and
adds no group inputs; a signing reply adds its commitment to the received basis.
The generator and verification key are the initial two received points.

This is the full-field-nonce scheme of Fuchsbauer--Plouviez--Seurin,
EUROCRYPT 2020, Figure 3. This file defines the source game, not its reduction.
-/

open OracleComp OracleSpec AlgebraicGroupModel.Interaction

namespace Schnorr.AGM

abbrev Group (G : Type) := fun _ : Unit => G

inductive Request (M : Type) where
  | random (n : Nat)
  | hash (m : M)
  | sign (m : M)

def Reply (F M : Type) : Request M → Type
  | .random n => Fin (n + 1)
  | .hash _ => F
  | .sign _ => F

abbrev Adversary (F G M : Type) [Zero F] [AddMonoid G] [SMul F G] :=
  AlgebraicGroupModel.Interaction.Adversary F (Group G) Unit (Request M)
    (Reply F M) (M × F)

def initial {G : Type} (g pk : G) : Message Unit (Group G) := ⟨(), fun _ => [g, pk]⟩

def scalarReply {F G : Type} (z : F) : Message F (Group G) := ⟨z, fun _ => []⟩

def signingReply {F G : Type} (R : G) (z : F) : Message F (Group G) :=
  ⟨z, fun _ => [R]⟩

structure State (M : Type) where
  signed : List M := []
  malformed : Bool := false

section Game

variable {F G M : Type} [Field F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [DecidableEq M]

abbrev BaseSpec (F G M : Type) := unifSpec + (M × G →ₒ F)

/-- Rejected requests set a permanent failure bit; they cannot be used to win later. -/
def reject : StateT (State M) (OracleComp (BaseSpec F G M)) Unit :=
  modify fun s => { s with malformed := true }

def handler (g : G) (x : F) :
    QueryImpl (plainSpec (Group G) (Request M) (Reply F M))
      (StateT (State M) (OracleComp (BaseSpec F G M))) := by
  intro ⟨request, groups⟩
  cases request with
  | random n => exact do
      if groups () ≠ [] then reject
      let v ← liftM ((BaseSpec F G M).query (.inl n))
      pure ⟨v, fun _ => []⟩
  | hash m => exact do
      match groups () with
      | [R] =>
          let c ← liftM ((BaseSpec F G M).query (.inr (m, R)))
          pure (scalarReply c)
      | _ => reject; pure (scalarReply (0 : F))
  | sign m => exact do
      if groups () ≠ [] then
        reject
        pure (scalarReply (0 : F))
      else
        let a ← liftComp ($ᵗ F) (BaseSpec F G M)
        let R := a • g
        let c ← liftM ((BaseSpec F G M).query (.inr (m, R)))
        modify fun s => { s with signed := s.signed ++ [m] }
        pure (signingReply R (a + c * x))

/-- One key, adaptive hash/signing access, and fresh-message verification against the same RO. -/
def experiment (g : G) (A : Adversary F G M) : OracleComp (BaseSpec F G M) Bool := do
  let x ← liftComp ($ᵗ F) (BaseSpec F G M)
  let ((out, _basis), state) ← (A.run (handler g x) (initial g (x • g))).run {}
  match out.value.groups () with
  | [R] =>
      let (m, z) := out.value.data
      let c ← (BaseSpec F G M).query (.inr (m, R))
      pure (!state.malformed && decide (m ∉ state.signed ∧ z • g = R + c • (x • g)))
  | _ => pure false

/-- Lazy hashes share one initially empty cache, including internal signing and final verification. -/
noncomputable def game (g : G) (A : Adversary F G M) : ProbComp Bool :=
  (simulateQ (unifFwdImpl (M × G →ₒ F) + randomOracle (spec := M × G →ₒ F))
    (experiment g A)).run' ∅

end Game

end Schnorr.AGM
