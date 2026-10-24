import Proofs.Runtime.Caliper.BLSFullLayout
import Proofs.Runtime.Caliper.BLSExtractorAcceptance

/-! Complete Caliper BLS AGM program constructors. Only individual scalar/group
routines and local caller steps are parameters. Setup, lazy query handling,
transcript extraction and terminal control are generated here. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {M F G K A : Type}
    [Zero F] [Mul F] [Add F] [Sub F] [Neg F] [Div F] [SMul F G] [Add G] [SMul F K]
    (layout : Layouts w M F G K A)

/-- Named primitive code, with scratch-name reservations. No completed handler,
extractor or solver implementation is supplied through this record. -/
structure Routines where
  zeroValid : layout.tokens.rows.accumulation.cache.value.valid 0
  scalarMul : Implementation .unit layout.tokens.rows.accumulation.arithmetic.pair layout.scheme.cache.value (fun value => value.1 * value.2)
  scalarAdd : Implementation .unit layout.tokens.rows.accumulation.arithmetic.pair layout.scheme.cache.value (fun value => value.1 + value.2)
  scalarSub : Implementation .unit layout.tokens.rows.accumulation.arithmetic.pair layout.scheme.cache.value (fun value => value.1 - value.2)
  scalarNeg : Implementation .unit layout.scheme.cache.value layout.scheme.cache.value Neg.neg
  scalarDiv : Implementation .unit layout.tokens.rows.accumulation.arithmetic.pair layout.scheme.cache.value (fun value => value.1 / value.2)
  groupScale : Implementation .unit layout.scheme.response.scaleArgs layout.scheme.point (fun value => value.1 • value.2)
  groupAdd : Implementation .unit layout.scheme.response.points layout.scheme.point (fun value => value.1 + value.2)
  keyScale : Implementation .unit layout.setup.scaleArgs layout.key (fun value => value.1 • value.2)
  slots : Nat
  reserve : slots + 5 < 2 ^ w
  mulNames : NamesBound scalarMul.program.code slots
  addNames : NamesBound scalarAdd.program.code slots
  subNames : NamesBound scalarSub.program.code slots
  negNames : NamesBound scalarNeg.program.code slots
  divNames : NamesBound scalarDiv.program.code slots
  scaleNames : NamesBound groupScale.program.code slots
  groupAddNames : NamesBound groupAdd.program.code slots
  keyNames : NamesBound keyScale.program.code slots

omit [Zero F] [Mul F] [Add F] [Sub F] [Neg F] [Div F] [SMul F G] [Add G] [SMul F K] in
/-- Local caller initialization and continuation contain actual Caliper code. -/
structure Caller where
  advance : A × layout.Reply → layout.Next
  continuation : Realizer .unit (CallerStep.resume layout.good.control) (CallerStep.next layout.good.control) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : layout.key.Value → layout.Next
  initialCode : Realizer .unit layout.key.representation (CallerStep.next layout.good.control) initial
  initialNameFits : initialCode.savedBuffer < 2 ^ w

def goodStart (value : layout.setup.challenge.Value) : layout.key.Value × layout.good.service.store.Value :=
  layout.goodSetupView ⟨(value.val.2.2, value.val.1, [], [], []), (BLSSetup.good layout.setup).preserves value.val value.property⟩

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A)
    (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout) (draw : Interactive.Code w) (fuel : Nat)

abbrev zero := BLSTokens.zero layout.tokens routines.zeroValid
abbrev pairZero := BLSTokens.pairZero layout.tokens routines.zeroValid
def goodResponse := BLSResponse.good layout.scheme.response routines.groupScale
def badResponse := BLSResponse.bad layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
  (by have := routines.reserve; omega) routines.groupAddNames.buffers
def pairDraw := BLSCache.pairSampler (base := base) (key := key) (val := val) layout.scheme.cache layout.port draw

def goodExtractor : Interactive.Code w := BLSExtractor.goodCode layout.tokens routines.zeroValid P comparison correct
  routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers
  (by have := routines.reserve; omega) routines.divNames.buffers layout.port draw
def badExtractor : Interactive.Code w := BLSExtractor.badCode layout.tokens routines.zeroValid P comparison correct
  routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers
  (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers layout.port draw

def goodTail : Interactive.Code w := BLSCallerExtraction.program layout.good (zero layout routines) P comparison correct
  (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
  (layout.scheme.goodReserve routines.reserve) draw caller.advance caller.continuation caller.localNameFits
  layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.goodFits fuel (zero layout routines)
  (goodExtractor layout routines P comparison correct draw)
def badTail : Interactive.Code w := BLSCallerExtraction.program (base := base) (key := key) (val := .pair val val)
  layout.bad (pairZero layout routines) P comparison correct (badResponse layout routines)
  (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
    (by have := routines.reserve; omega) routines.groupAddNames.buffers)
  (layout.scheme.badReserve routines.reserve) (pairDraw layout draw) caller.advance caller.continuation caller.localNameFits
  layout.key.representation caller.initial caller.initialCode caller.initialNameFits layout.setup.badFits fuel (zero layout routines)
  (badExtractor layout routines P comparison correct draw)
def goodCode : Interactive.Code w := .seq (BLSSetup.goodCode layout.setup) (goodTail layout routines P comparison correct caller draw fuel)
def badCode : Interactive.Code w :=
  .seq (BLSSetup.badCode layout.setup layout.port draw routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega))
    (badTail layout routines P comparison correct caller draw fuel)

variable (drawSource : ProbComp layout.scheme.cache.value.Value)
def goodExtract := BLSExtractor.goodDenote layout.tokens routines.zeroValid P comparison correct
  routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarDiv routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers
  (by have := routines.reserve; omega) routines.divNames.buffers drawSource
def badExtract := BLSExtractor.badDenote layout.tokens routines.zeroValid P comparison correct
  routines.scalarMul routines.scalarAdd routines.scalarSub routines.scalarNeg routines.scalarDiv routines.mulNames.buffers routines.addNames.buffers routines.subNames.buffers
  (by have := routines.reserve; omega) routines.negNames.buffers routines.divNames.buffers drawSource
def pairSource := PairSampling.denote layout.scheme.cache.value layout.scheme.cache.value layout.scheme.cache.pairValueFits drawSource drawSource
def goodTailSource := BLSCallerExtraction.denote layout.good (zero layout routines) P comparison correct
  (goodResponse layout routines) (BLSResponse.good_buffers layout.scheme.response routines.groupScale routines.scaleNames.buffers)
  (layout.scheme.goodReserve routines.reserve) caller.advance caller.initial fuel drawSource (zero layout routines)
  (goodExtract layout routines P comparison correct drawSource)
def badTailSource := BLSCallerExtraction.denote (base := base) (key := key) (val := .pair val val) layout.bad (pairZero layout routines) P comparison correct
  (badResponse layout routines) (BLSResponse.bad_buffers layout.scheme.response routines.groupScale routines.groupAdd routines.scaleNames.buffers
    (by have := routines.reserve; omega) routines.groupAddNames.buffers)
  (layout.scheme.badReserve routines.reserve) caller.advance caller.initial fuel (pairSource layout drawSource) (zero layout routines)
  (badExtract layout routines P comparison correct drawSource)
def badStart (value : layout.setup.challenge.Value) : ProbComp (layout.key.Value × layout.bad.service.store.Value) :=
  layout.badSetupView <$> BLSSetup.badSource layout.setup drawSource routines.keyScale routines.keyNames.buffers (by have := routines.reserve; omega) value
def goodSource (value : layout.setup.challenge.Value) : ProbComp layout.scheme.cache.value.Value :=
  goodTailSource layout routines P comparison correct caller fuel drawSource (goodStart layout value)
def badSource (value : layout.setup.challenge.Value) : ProbComp layout.scheme.cache.value.Value :=
  badStart layout routines drawSource value >>= badTailSource layout routines P comparison correct caller fuel drawSource
end Signatures.Runtime.CaliperBackend.BLSFull
