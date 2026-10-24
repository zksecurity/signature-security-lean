import Proofs.Runtime.Caliper.UniformQuery
import Proofs.Runtime.Caliper.EncodedConstant
import Proofs.Runtime.Caliper.Finite
import Proofs.Runtime.Caliper.InteractiveInvariantViews

/-! An executed fixed-range draw through the uniform word port. The program
writes the requested range, invokes the oracle, and copies the returned index.
The dependent reply invariant justifies its finite output type; no table of
possible coins or uncharged local sampling operation is used. -/
namespace Signatures.Runtime.CaliperBackend.UniformSampling
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)
    (n : Fin (bound + 1))

def input : Layout w Unit := DataImplementation.unitLayout w
def output : Layout w (Fin (n.val + 1)) :=
  Finite.layout n.val hw (by have := n.isLt; omega)

def prepare : Realizer .unit (input (w := w)).representation (UniformQuery.request bound hw fits)
    (fun _ => n) :=
  (Implementation.constant (input (w := w)) (Layout.all (UniformQuery.request bound hw fits))
    ⟨n, trivial⟩ hw).program.viewOutput (UniformQuery.request bound hw fits) (fun _ => n) (fun _ => rfl)

abbrev Reply := {packet : UniformQuery.Reply bound // packet.1 = n}
def middle : Representation w (Reply bound n) :=
  (UniformQuery.reply bound hw fits).restrict (fun packet => packet.1 = n)

def narrow (packet : UniformQuery.Reply bound) : Reply bound n :=
  if equal : packet.1 = n then ⟨packet, equal⟩ else ⟨⟨n, 0⟩, rfl⟩

theorem narrow_same (sampled : Fin (n.val + 1)) :
    narrow bound n ⟨n, sampled⟩ = ⟨⟨n, sampled⟩, rfl⟩ := by
  unfold narrow
  rw [dite_eq_left rfl]

def answer (packet : Reply bound n) : (output bound hw fits n).Value :=
  ⟨⟨packet.val.2.val, by simpa only [packet.property] using packet.val.2.isLt⟩, trivial⟩

def finish : Realizer .unit (middle bound hw fits n) (output bound hw fits n).representation
    (answer bound hw fits n) :=
  Assembly.realizer .unit (by decide) _ _ _ [.read 0 1] hw rfl
    (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 2 at size
      simp only [List.mem_singleton] at member
      subst operand
      change 0 ≠ 1 ∧ 1 < (before.bufs 0).size ∧ 1 < 2 ^ w
      rw [size]
      exact ⟨by decide, by decide, by omega⟩)
    (by
      intro value before holds
      have bytes : before.bufs 0 =
          #[BitVec.ofNat w value.val.1.val, BitVec.ofNat w value.val.2.val] :=
        Array.toList_inj.mp holds.2.1
      change [(before.bufs 0)[1]?.getD 0] = [BitVec.ofNat w value.val.2.val]
      rw [bytes]
      rfl)

def requestCode : Interactive.Code w := .seq (.compute (prepare bound hw fits n).code) .query
def code : Interactive.Code w := .seq (requestCode bound hw fits n) (.compute (finish bound hw fits n).code)

def source : ProbComp (output bound hw fits n).Value :=
  (fun value => (⟨value, trivial⟩ : (output bound hw fits n).Value)) <$> (unifSpec.query n.val)

theorem prefix_refines : Interactive.Refines (UniformQuery.port bound hw fits) .unit
    (input (w := w)).representation (middle bound hw fits n)
    (fun _ => narrow bound n <$> UniformQuery.source bound n) (requestCode bound hw fits n) := by
  have prepared := (Interactive.Refines.compute (UniformQuery.port bound hw fits) .unit
    (prepare bound hw fits n)).seq (UniformQuery.refines bound hw fits)
  have raw : Interactive.Refines (UniformQuery.port bound hw fits) .unit
      (input (w := w)).representation (UniformQuery.reply bound hw fits)
      (fun _ => UniformQuery.source bound n) (requestCode bound hw fits n) := by
    simpa only [pure_bind, requestCode] using prepared
  apply raw.viewOutputOnSupport (middle bound hw fits n) (narrow bound n)
  intro value packet reached
  obtain ⟨sampled, _, rfl⟩ := (show ∃ sampled ∈ support (unifSpec.query n.val : ProbComp (Fin (n.val + 1))),
      (⟨n, sampled⟩ : UniformQuery.Reply bound) = packet from by
    simpa only [UniformQuery.source, support_map, Set.mem_image] using reached)
  rw [narrow_same]
  rfl

theorem refines : Interactive.Refines (UniformQuery.port bound hw fits) .unit
    (input (w := w)).representation (output bound hw fits n).representation
    (fun _ => source bound hw fits n) (code bound hw fits n) := by
  have composed := (prefix_refines bound hw fits n).seq
    (Interactive.Refines.compute (UniformQuery.port bound hw fits) .unit (finish bound hw fits n))
  convert composed using 1
  · funext value
    simp only [bind_pure_comp, Functor.map_map, UniformQuery.source, source, narrow_same, answer]
  · rfl

theorem uniform : Subtype.val <$> source bound hw fits n = ($ᵗ (Fin (n.val + 1)) : ProbComp _) := by
  simp only [source, Functor.map_map]
  rfl

end Signatures.Runtime.CaliperBackend.UniformSampling
