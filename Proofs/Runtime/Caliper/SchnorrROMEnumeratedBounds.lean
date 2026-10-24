import Proofs.Runtime.Caliper.SchnorrROMEnumeratedSource

/-! Constant local caller costs, independent of the scalar domain's cardinality.
These feed the existing private-service/pair/signing resource theorems. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
open Caliper BoundedSource
variable {w : Nat} {F : Type} (params : Parameters w F)

theorem initial_time (input : (tape params).unit.Value) : (initialCode params).time input ≤ 16 :=
  Assembly.code_time_unit_le _
theorem initial_words : descriptionWords (initialCode params).code ≤ 66 := Assembly.code_descriptionWords_le _

theorem continuation_time (input : Unit × Response (layout params)) : (continuation params).time input ≤ 38 := by
  have args := Assembly.code_time_unit_le (w := w) [.read 0 1, .literal (BitVec.ofNat w (params.bound + 1))]
  have tagged := Assembly.code_time_unit_le (w := w) (Construction.taggedOperands 0 1 0)
  change (arguments params).time input ≤ 16 at args
  change (Assembly.code (Construction.taggedOperands (w := w) 0 1 0)).staticTime .unit ≤ 16 at tagged
  change (arguments params).time input + 6 + (Assembly.code (Construction.taggedOperands (w := w) 0 1 0)).staticTime .unit ≤ 38
  omega

theorem continuation_words : descriptionWords (continuation params).code ≤ 161 := by
  have args := Assembly.code_descriptionWords_le (w := w) [.read 0 1, .literal (BitVec.ofNat w (params.bound + 1))]
  have tagged := Assembly.code_descriptionWords_le (w := w) (Construction.taggedOperands 0 1 0)
  change descriptionWords (arguments params).code ≤ 66 at args
  change descriptionWords (Assembly.code (Construction.taggedOperands (w := w) 0 1 0)) ≤ 66 at tagged
  change descriptionWords (((arguments params).code ;; WordBinary.code .umod) ;;
    Assembly.code (Construction.taggedOperands 0 1 0)) ≤ 161
  rw [descriptionWords_seq, descriptionWords_seq, WordBinary.descriptionWords_eq]
  omega

theorem initial_names : NamesBound (initialCode params).code 3 := by
  have bounded := Assembly.code_names (w := w) [.literal 1, .literal (BitVec.ofNat w params.bound)] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])
  exact ⟨bounded.1, bounded.2.trans (by decide)⟩
theorem continuation_names : NamesBound (continuation params).code 3 := by
  have args := (Assembly.code_names (w := w) [.read 0 1, .literal (BitVec.ofNat w (params.bound + 1))] 1
    (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).1
  have tagged := (Assembly.code_names (w := w) (Construction.taggedOperands 0 1 0) 1
    (by simp [Construction.taggedOperands, Assembly.SourcesBound, Assembly.Operand.SourcesBound, Assembly.reads])).1
  refine ⟨?_, (continuation_buffers params).trans (by decide)⟩
  change max (max (registerSlots (arguments params).code) 3)
    (registerSlots (Assembly.code (Construction.taggedOperands 0 1 0))) ≤ 3
  change registerSlots (arguments params).code ≤ 3 at args
  omega

theorem initial_headroom : (caller params).initialCode.code.memBound + 2 < 2 ^ w := by
  have := initial_buffers params; have := params.wordFits
  change (initialCode params).code.memBound + 2 < _
  omega
theorem continuation_headroom : (caller params).continuation.code.memBound + 2 < 2 ^ w := by
  have := continuation_buffers params; have := params.wordFits
  change (continuation params).code.memBound + 2 < _
  omega

variable [Zero F]

theorem pair_time : Interactive.TimeBoundOn (Pair.ready (layout params) 1) (Fresh.port (tape params)) .unit
    (Read.tapes (tape params)).representation (Pair.code (layout params) (caller params) trivial 1)
    (Pair.timeBudget (layout params) trivial 38 16 1) :=
  Pair.time_bound (layout params) (caller params) trivial 1 38 16 (continuation_time params) (initial_time params)
theorem pair_names : WordIO.NamesAccounted
    ((Pair.code (layout params) (caller params) trivial 1).lower (Fresh.port (tape params)))
    (PrivateSampler.nameBudget (layout params) trivial 3) :=
  Pair.names (layout params) (caller params) trivial 1 3 (continuation_names params).accounted (initial_names params).accounted
theorem pair_descriptionFits : ((Pair.code (layout params) (caller params) trivial 1).lower (Fresh.port (tape params))).DescriptionFits :=
  Pair.descriptionFits (layout params) (caller params) trivial 1
    (by have := continuation_headroom params; omega) (by have := initial_headroom params; omega)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated
