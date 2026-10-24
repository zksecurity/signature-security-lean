import Proofs.Runtime.Caliper.SchnorrAGMFreshBounds
import Proofs.Runtime.BackendSchnorrAGMCache

/-! The executed Schnorr cache combines bounded lookup/insertion with the
constructed stateful fresh routine. Key equality scans encoded message/point
words. Only local scalar sampling and addition implementations are supplied. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native

inductive Comparison : Ty CryptoAtom → Ty CryptoAtom → Type
  | equal : Comparison (.pair cacheKeyTy cacheKeyTy) .bool
def primitives (F G M : Type) [DecidableEq G] [DecidableEq M] :
    Primitives (cryptoBase F G Unit M M) Comparison where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
def comparison : Expr Comparison [cacheKeyTy, cacheKeyTy] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
theorem comparison_correct (F G M : Type) [DecidableEq G] [DecidableEq M] (lhs rhs : M × G) :
    comparison.denote (primitives F G M) (lhs, rhs, ()) = decide (lhs = rhs) := rfl

variable {w qH qS : Nat} {M F G I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)
    (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  StatefulCacheRead.code (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M)
    (Fresh.code layout zeroValid add addBuffers slotsFit port sampler)

def source (sampler : OracleComp spec layout.scalar.Value) :
    layout.cache.input.Value × (saved layout).Value →
      OracleComp spec ((CacheRead.output layout.cache).Value × (saved layout).Value) :=
  StatefulCacheRead.denote (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    (model layout) (primitives F G M) comparison (comparison_correct F G M) (Fresh.denote layout sampler)

def timeBudget (addTime sampleTime : Nat) : Nat :=
  StatefulCacheRead.timeBudget (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    (model layout) (Fresh.timeBudget layout addTime sampleTime)
def codeBudget (addWords sampleWords : Nat) : Nat :=
  StatefulCacheRead.codeBudget (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    (model layout) (Fresh.codeBudget layout addWords sampleWords)

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (model layout).input (model layout).output
      (source layout sampleSource) (code layout zeroValid add addBuffers slotsFit port sampler) :=
  StatefulCacheRead.refines (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M) _ _
    (Fresh.refines layout zeroValid add addBuffers slotsFit port sampleCorrect)

theorem time_bound {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) {addTime sampleTime : Nat}
    (addBound : ∀ value, add.program.time value ≤ addTime)
    (sampleBound : Interactive.TimeBound port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound port .unit (model layout).input (code layout zeroValid add addBuffers slotsFit port sampler)
      (timeBudget layout addTime sampleTime) :=
  StatefulCacheRead.time_bound (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M)
    (Fresh.refines layout zeroValid add addBuffers slotsFit port sampleCorrect)
    (Fresh.time_bound layout zeroValid add addBuffers slotsFit port sampleCorrect addBound sampleBound)

theorem code_bound (sampler : Interactive.Code w) {addWords sampleWords : Nat}
    (addBound : descriptionWords add.program.code ≤ addWords)
    (sampleBound : (sampler.lower port).descriptionWords ≤ sampleWords) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).descriptionWords ≤
      codeBudget layout addWords sampleWords :=
  StatefulCacheRead.code_bound (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M) _
    (Fresh.code_bound layout zeroValid add addBuffers slotsFit port sampler addBound sampleBound)

theorem names (sampler : Interactive.Code w) {sampleSlots : Nat}
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots) :
    WordIO.NamesAccounted ((code layout zeroValid add addBuffers slotsFit port sampler).lower port)
      (max 5 (Fresh.nameBudget slots sampleSlots)) :=
  StatefulCacheRead.names (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M) _
    (Fresh.names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames)

theorem descriptionFits (sampler : Interactive.Code w) {sampleSlots : Nat}
    (sampleFits : (sampler.lower port).DescriptionFits)
    (addNames : NamesBound add.program.code slots) (sampleNames : WordIO.NamesBound (sampler.lower port) sampleSlots)
    (reserve : max slots sampleSlots + 2 < 2 ^ w) :
    ((code layout zeroValid add addBuffers slotsFit port sampler).lower port).DescriptionFits :=
  StatefulCacheRead.descriptionFits (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    port (model layout) (primitives F G M) comparison (comparison_correct F G M) _
    (Fresh.descriptionFits layout zeroValid add addBuffers slotsFit port sampler sampleFits sampleNames (by omega))
    (Fresh.names layout zeroValid add addBuffers slotsFit port sampler addNames sampleNames)
    (by unfold Fresh.nameBudget; have := layout.wordFits; omega)

section Original
variable {w qH qS : Nat} {M F G I : Type} [Field F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (layout : Layouts w M F G qH qS)

theorem source_value (sampler : OracleComp spec layout.scalar.Value)
    (value : layout.cache.input.Value × (saved layout).Value) :
    (fun result => (result.1.val, result.2.val)) <$> source layout sampler value =
      match cacheMap value.1.val.2.2.1 value.1.val.1 with
      | some entry => pure ((entry, value.1.val.2.2.1), value.2.val)
      | none => (fun challenge => let fresh := Signatures.Runtime.SchnorrAGM.Native.freshValue (challenge, value.2.val)
          ((fresh.1, (value.1.val.1, fresh.1) :: value.1.val.2.2.1), fresh.2)) <$> (Subtype.val <$> sampler) := by
  have erased := congrArg
    (fun computation : OracleComp spec ((EncodedEntry F × List ((M × G) × EncodedEntry F)) × (saved layout).Value) =>
      (fun result => (result.1, result.2.val)) <$> computation)
    (StatefulCacheRead.denote_value (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
      (model layout) (primitives F G M) comparison (comparison_correct F G M) (Fresh.denote layout sampler) value)
  have looked : (lookupExpr (val := entryTy) comparison).denote (primitives F G M) value.1.val =
      lookupValue value.1.val.1 value.1.val.2.1 value.1.val.2.2.1 := by
    simpa only [Expr.run_value] using lookupExpr_value (val := entryTy) (primitives F G M) comparison
      (comparison_correct F G M) value.1.val.1 value.1.val.2.1 value.1.val.2.2.1
  rw [looked, lookupValue_cacheMap] at erased
  have joint := (PFunctor.FreeM.comp_map
    (fun result : (EncodedEntry F × List ((M × G) × EncodedEntry F)) × (saved layout).Value =>
      (result.1, result.2.val))
    (fun result : (CacheRead.output layout.cache).Value × (saved layout).Value => (result.1.val, result.2))
    (source layout sampler value)).trans erased
  refine joint.trans ?_
  cases found : cacheMap value.1.val.2.2.1 value.1.val.1 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, map_pure,
      Fresh.denote, Functor.map_map]
  refine (PFunctor.FreeM.comp_map _ _ _).symm.trans ?_
  exact (PFunctor.FreeM.comp_map _ _ _).symm

end Original
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache
