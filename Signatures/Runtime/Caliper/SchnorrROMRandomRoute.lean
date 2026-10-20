import Signatures.Runtime.Caliper.SchnorrROMRandomLayout
import Signatures.Runtime.Caliper.ReorderTail

/-! Executed permutations move both tapes next to the request and restore the
complete source store after the reply. The existing three-block copier supplies
both routes; mathematical views merely reassociate byte-identical products. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Random
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem prepareFits : (Reply.range config.handler.sampler.tape).representation.encoding.words +
    config.handler.caches.representation.encoding.words + (Read.store config.handler.sampler.tape).representation.encoding.words < 2 ^ w := by
  have := (input config).representation.fits
  change 1 + (_ + _) < _ at this
  change 1 + config.handler.caches.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words < _
  omega
def prepareInputValue (value : (input config).Value) :
    ((Reply.range config.handler.sampler.tape).Value × config.handler.caches.Value) × (Read.store config.handler.sampler.tape).Value :=
  ((⟨value.val.1, value.property.1.1⟩, context config value),
    ⟨value.val.2.2, ⟨value.property.1.2.2.1, value.property.2⟩, value.property.1.2.2.2⟩)
def prepare : Realizer .unit (input config).representation (prepared config) (prepareValue config) :=
  ((ReorderTail.realizer (Reply.range config.handler.sampler.tape).representation config.handler.caches.representation
    (Read.store config.handler.sampler.tape).representation config.sampler.wordFits (prepareFits config)).viewInput
      (input config).representation (prepareInputValue config) (by
        intro value
        change _ ++ (_ ++ _) = (_ ++ _) ++ _
        exact (List.append_assoc _ _ _).symm)).viewOutput (prepared config)
          (prepareValue config)
          (fun _ => rfl)

theorem finishFits : (reply config).representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words +
    config.handler.caches.representation.encoding.words < 2 ^ w := by
  have := (finished config).fits
  change (1 + (1 + _)) + _ < _ at this
  change (1 + 1) + _ + _ < _
  omega
def finishInputValue (value : (Reply.privateOutput config.handler.sampler.tape).Value × config.handler.caches.Value) :
    ((reply config).Value × (Read.tapes config.handler.sampler.tape).Value) × config.handler.caches.Value :=
  ((⟨(value.1.val.1, value.1.val.2.1), ⟨value.1.property.1.1, value.1.property.1.2.1⟩, value.1.property.2⟩,
    ⟨value.1.val.2.2, value.1.property.1.2.2⟩), value.2)
def finish : Realizer .unit (finished config) (output config).representation (finishValue config) :=
  ((ReorderTail.realizer (reply config).representation (Read.tapes config.handler.sampler.tape).representation
    config.handler.caches.representation config.sampler.wordFits (finishFits config)).viewInput (finished config)
      (finishInputValue config) (by
        intro value
        change (_ ++ (_ ++ _)) ++ _ = ((_ ++ _) ++ _) ++ _
        simp only [List.append_assoc]
        rfl)).viewOutput (output config).representation
          (finishValue config)
          (by intro value; change _ ++ (_ ++ _) = (_ ++ _) ++ _; exact (List.append_assoc _ _ _).symm)

theorem prepare_time (value) : (prepare config).time value ≤ 8 * (prepared config).encoding.words := by
  have bound := ReorderTail.time (Reply.range config.handler.sampler.tape).representation config.handler.caches.representation
    (Read.store config.handler.sampler.tape).representation config.sampler.wordFits (prepareFits config) (prepareInputValue config value)
  exact bound.trans (by change 8 * (1 + _ + _) ≤ 8 * ((1 + _) + _); omega)
theorem finish_time (value) : (finish config).time value ≤ 8 * (output config).representation.encoding.words := by
  have bound := ReorderTail.time (reply config).representation (Read.tapes config.handler.sampler.tape).representation
    config.handler.caches.representation config.sampler.wordFits (finishFits config) (finishInputValue config value)
  exact bound.trans (by change 8 * (2 + _ + _) ≤ 8 * (2 + (_ + _)); omega)
theorem prepare_words : descriptionWords (prepare config).code ≤ 26 * (prepared config).encoding.words + 14 := by
  have bound := ReorderTail.words (Reply.range config.handler.sampler.tape).representation config.handler.caches.representation
    (Read.store config.handler.sampler.tape).representation config.sampler.wordFits (prepareFits config)
  exact bound.trans (by change 26 * (1 + _ + _) + 14 ≤ 26 * ((1 + _) + _) + 14; omega)
theorem finish_words : descriptionWords (finish config).code ≤ 26 * (output config).representation.encoding.words + 14 := by
  have bound := ReorderTail.words (reply config).representation (Read.tapes config.handler.sampler.tape).representation
    config.handler.caches.representation config.sampler.wordFits (finishFits config)
  exact bound.trans (by change 26 * (2 + _ + _) + 14 ≤ 26 * (2 + (_ + _)) + 14; omega)
theorem prepare_buffers : (prepare config).code.memBound ≤ 2 :=
  (Assembly.code_names _ 1 (ReorderTail.sources _ _ _)).2
theorem finish_buffers : (finish config).code.memBound ≤ 2 :=
  (Assembly.code_names _ 1 (ReorderTail.sources _ _ _)).2
theorem prepare_names (slots : Nat) : NamesAccounted (prepare config).code slots :=
  Assembly.code_namesAccounted _ slots (ReorderTail.sources _ _ _)
theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots :=
  Assembly.code_namesAccounted _ slots (ReorderTail.sources _ _ _)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Random
