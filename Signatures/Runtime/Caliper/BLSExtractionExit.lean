import Signatures.Runtime.Caliper.BLSCallerFinishBounds
import Signatures.Runtime.Caliper.BLSExtractorAcceptance

/-! Both actual BLS AGM extractor branches, including caller-exit dispatch,
configuration removal, cutoff zero and scalar projection. Only primitive
routine and sampling contracts are parameters. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractionExit
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)]
    (layout : BLSTokens.Layouts w (key.Value base) G (val.Value base))
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (mul : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 * value.2))
    (add : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 + value.2))
    (sub : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 - value.2))
    (negate : Implementation .unit layout.rows.accumulation.cache.value layout.rows.accumulation.cache.value Neg.neg)
    (divide : Implementation .unit layout.rows.accumulation.arithmetic.pair layout.rows.accumulation.cache.value (fun value => value.1 / value.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots) (addBuffers : add.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 4 < 2 ^ w) (negBuffers : negate.program.code.memBound ≤ slots) (divBuffers : divide.program.code.memBound ≤ slots)


variable {C Pending : Type} (config : Representation w C) (pending : Representation w Pending)
    (goodFits : 1 + max (BLSExtractorFrame.forgery layout.good).representation.encoding.words pending.encoding.words +
      config.encoding.words + (BLSExtractorFrame.store layout.good).representation.encoding.words < 2 ^ w)
    (badFits : 1 + max (BLSExtractorFrame.forgery layout.bad).representation.encoding.words pending.encoding.words +
      config.encoding.words + (BLSExtractorFrame.store layout.bad).representation.encoding.words < 2 ^ w)
variable {I : Type} {spec : OracleSpec I}

def goodCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  BLSCallerFinish.code layout.good config pending goodFits (BLSTokens.zero layout zeroValid)
    (BLSExtractor.goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar)
def goodDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) :=
  BLSCallerFinish.denote (P := Pending) (C := C) layout.good (BLSTokens.zero layout zeroValid)
    (BLSExtractor.goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers source)

def badCode (port : Interactive.Port w spec) (scalar : Interactive.Code w) : Interactive.Code w :=
  BLSCallerFinish.code layout.bad config pending badFits (BLSTokens.zero layout zeroValid)
    (BLSExtractor.badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar)
def badDenote (source : OracleComp spec layout.rows.accumulation.cache.value.Value) :=
  BLSCallerFinish.denote (P := Pending) (C := C) layout.bad (BLSTokens.zero layout zeroValid)
    (BLSExtractor.badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers source)

variable (port : Interactive.Port w spec) {scalar : Interactive.Code w}
    {source : OracleComp spec layout.rows.accumulation.cache.value.Value}
    (scalarCorrect : Interactive.Refines port .unit layout.rows.accumulation.cache.lookup.unit.representation
      layout.rows.accumulation.cache.value.representation (fun _ => source) scalar)
include scalarCorrect in
omit [Neg (val.Value base)] in
theorem good_refines :
    Interactive.RefinesOn (BLSCallerFinish.ready layout.good (BLSExtractor.goodReady layout)) port .unit
      (BLSCallerFinish.input layout.good config pending goodFits) layout.rows.accumulation.cache.value.representation
      (goodDenote layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers (C := C) (Pending := Pending) source)
      (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers config pending goodFits port scalar) :=
  BLSCallerFinish.refines layout.good config pending goodFits port
    (BLSExtractor.good_refines layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect) (BLSTokens.zero layout zeroValid)
include scalarCorrect in
theorem bad_refines :
    Interactive.RefinesOn (BLSCallerFinish.ready layout.bad (BLSExtractor.badReady layout)) port .unit
      (BLSCallerFinish.input layout.bad config pending badFits) layout.rows.accumulation.cache.value.representation
      (badDenote layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers (C := C) (Pending := Pending) source)
      (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers config pending badFits port scalar) :=
  BLSCallerFinish.refines layout.bad config pending badFits port
    (BLSExtractor.bad_refines layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalarCorrect) (BLSTokens.zero layout zeroValid)

variable {scalarTime scalarWords mulTime mulWords addTime addWords subTime subWords negTime negWords divTime divWords : Nat}
    (scalarTimeBound : Interactive.TimeBound port .unit layout.rows.accumulation.cache.lookup.unit.representation scalar scalarTime)
    (scalarWordsBound : (scalar.lower port).descriptionWords ≤ scalarWords)
    (mulBound : mul.BoundedBy mulTime mulWords) (addBound : add.BoundedBy addTime addWords)
    (subBound : sub.BoundedBy subTime subWords) (negBound : negate.BoundedBy negTime negWords) (divBound : divide.BoundedBy divTime divWords)
include scalarCorrect scalarTimeBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_time :
    Interactive.TimeBoundOn (BLSCallerFinish.ready layout.good (BLSExtractor.goodReady layout)) port .unit
      (BLSCallerFinish.input layout.good config pending goodFits)
      (goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers config pending goodFits port scalar)
      (BLSCallerFinish.timeBudget layout.good config pending goodFits (BLSExtractor.goodTime layout scalarTime mulTime addTime subTime divTime)) :=
  BLSCallerFinish.time_bound layout.good config pending goodFits port
    (BLSExtractor.good_refines layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect)
    (BLSExtractor.good_time layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalarCorrect scalarTimeBound mulBound addBound subBound divBound)
    (BLSTokens.zero layout zeroValid)
include scalarWordsBound mulBound addBound subBound divBound in
omit [Neg (val.Value base)] in
theorem good_words :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers config pending goodFits port scalar).lower port).descriptionWords ≤
      BLSCallerFinish.codeBudget layout.good config pending goodFits (BLSExtractor.goodWords layout scalarWords mulWords addWords subWords divWords) :=
  BLSCallerFinish.code_bound layout.good config pending goodFits port
    (BLSExtractor.good_words layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar scalarWordsBound mulBound addBound subBound divBound) (BLSTokens.zero layout zeroValid)
include scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound in
theorem bad_time :
    Interactive.TimeBoundOn (BLSCallerFinish.ready layout.bad (BLSExtractor.badReady layout)) port .unit
      (BLSCallerFinish.input layout.bad config pending badFits)
      (badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers config pending badFits port scalar)
      (BLSCallerFinish.timeBudget layout.bad config pending badFits (BLSExtractor.badTime layout scalarTime mulTime addTime subTime negTime divTime)) :=
  BLSCallerFinish.time_bound layout.bad config pending badFits port
    (BLSExtractor.bad_refines layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalarCorrect)
    (BLSExtractor.bad_time layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalarCorrect scalarTimeBound mulBound addBound subBound negBound divBound)
    (BLSTokens.zero layout zeroValid)
include scalarWordsBound mulBound addBound subBound negBound divBound in
theorem bad_words :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers config pending badFits port scalar).lower port).descriptionWords ≤
      BLSCallerFinish.codeBudget layout.bad config pending badFits (BLSExtractor.badWords layout scalarWords mulWords addWords subWords negWords divWords) :=
  BLSCallerFinish.code_bound layout.bad config pending badFits port
    (BLSExtractor.bad_words layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar scalarWordsBound mulBound addBound subBound negBound divBound) (BLSTokens.zero layout zeroValid)

variable {drawNames names : Nat}
    (drawNamesBound : WordIO.NamesBound (scalar.lower port) drawNames)
    (mulNames : NamesAccounted mul.program.code names) (addNames : NamesAccounted add.program.code names)
    (subNames : NamesAccounted sub.program.code names) (negNames : NamesAccounted negate.program.code names)
    (divNames : NamesAccounted divide.program.code names)
    (scalarFits : (scalar.lower port).DescriptionFits) (namesFit : drawNames + 4 < 2 ^ w)
include drawNamesBound mulNames addNames subNames divNames in
omit [Neg (val.Value base)] in
theorem good_names :
    WordIO.NamesAccounted ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers config pending goodFits port scalar).lower port) (BLSExtractor.nameBudget drawNames names) :=
  BLSCallerFinish.names layout.good config pending goodFits port
    (BLSExtractor.good_names layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar drawNamesBound mulNames addNames subNames divNames) (BLSTokens.zero layout zeroValid)
include scalarFits drawNamesBound namesFit in
omit [Neg (val.Value base)] in
theorem good_descriptionFits :
    ((goodCode layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers config pending goodFits port scalar).lower port).DescriptionFits :=
  BLSCallerFinish.descriptionFits layout.good config pending goodFits port (BLSTokens.zero layout zeroValid)
    (BLSExtractor.good_descriptionFits layout zeroValid P comparison correct mul add sub divide mulBuffers addBuffers subBuffers reserve divBuffers port scalar scalarFits drawNamesBound namesFit)
include drawNamesBound mulNames addNames subNames negNames divNames in
theorem bad_names :
    WordIO.NamesAccounted ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers config pending badFits port scalar).lower port) (BLSExtractor.nameBudget drawNames names) :=
  BLSCallerFinish.names layout.bad config pending badFits port
    (BLSExtractor.bad_names layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar drawNamesBound mulNames addNames subNames negNames divNames) (BLSTokens.zero layout zeroValid)
include scalarFits drawNamesBound namesFit in
theorem bad_descriptionFits :
    ((badCode layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers config pending badFits port scalar).lower port).DescriptionFits :=
  BLSCallerFinish.descriptionFits layout.bad config pending badFits port (BLSTokens.zero layout zeroValid)
    (BLSExtractor.bad_descriptionFits layout zeroValid P comparison correct mul add sub negate divide mulBuffers addBuffers subBuffers reserve negBuffers divBuffers port scalar scalarFits drawNamesBound namesFit)
end Signatures.Runtime.CaliperBackend.BLSExtractionExit
