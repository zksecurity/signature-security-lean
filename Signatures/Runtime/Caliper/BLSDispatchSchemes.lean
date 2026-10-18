import Signatures.Runtime.Caliper.BLSDispatchSource

/-! Both stored-tag BLS AGM dispatchers, constructed from scalar sampling,
scalar multiplication and addition. The challenge configuration is stored data.
Time charges the executed branch; code space includes both branches. -/

namespace Signatures.Runtime.CaliperBackend.BLSDispatch
open Caliper BoundedSource OracleComp OracleSpec
open BLSReply (SchemeLayouts)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [SMul (val.Value base) G]
    (layout : SchemeLayouts w (key.Value base) (val.Value base) G)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (scalar : Interactive.Code w)
    (scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)

def goodCode : Interactive.Code w :=
  code layout.good default P comparison correct port scalar (BLSResponse.good layout.response scale)
    (BLSResponse.good_buffers layout.response scale scaleBuffers) (layout.goodReserve reserve)

variable [Add G] (add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2))
    (addBuffers : add.program.code.memBound ≤ slots)

def badCode : Interactive.Code w :=
  code (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) P comparison correct port
    (BLSCache.pairSampler layout.cache port scalar)
    (BLSResponse.bad layout.response scale add scaleBuffers (by omega) addBuffers)
    (BLSResponse.bad_buffers layout.response scale add scaleBuffers (by omega) addBuffers) (layout.badReserve reserve)

variable {source : ProbComp layout.cache.value.Value}
    (scalarCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => source) scalar)
    {scalarTime scalarWords scaleTime scaleWords addTime addWords : Nat}
    (scalarBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation scalar scalarTime)
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (addBound : add.BoundedBy addTime addWords)

include scalarCorrect scalarBound scaleBound in
omit [Add G] in
theorem good_time : Interactive.TimeBound port .unit (input layout.good default).representation
    (goodCode layout default P comparison correct port scalar scale scaleBuffers reserve)
    (timeBudget layout.good scalarTime (fun _ => BLSResponse.goodTime layout.response scaleTime)) :=
  time_bound layout.good default P comparison correct port scalar _ _ _ scalarCorrect scalarBound
    (BLSResponse.good_bounded layout.response scale scaleBound)

include scalarCorrect scalarBound scaleBound addBound in
theorem bad_time : Interactive.TimeBound port .unit (input layout.bad (layout.pairDefault default)).representation
    (badCode layout default P comparison correct port scalar scale scaleBuffers reserve add addBuffers)
    (timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.timeBudget layout.cache.value layout.cache.value scalarTime scalarTime)
      (fun signing => BLSResponse.badTime layout.response signing scaleTime addTime)) :=
  time_bound (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) P comparison correct port _ _ _ _
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect scalarBound scalarBound)
    (BLSResponse.bad_bounded layout.response scale add scaleBound addBound scaleBuffers (by omega) addBuffers)

include scaleBound in
omit [Add G] in
theorem good_words (scalarCodeBound : (scalar.lower port).descriptionWords ≤ scalarWords) :
    ((goodCode layout default P comparison correct port scalar scale scaleBuffers reserve).lower port).descriptionWords ≤
      codeBudget layout.good scalarWords (fun _ => BLSResponse.goodWords layout.response scaleWords) :=
  code_bound layout.good default P comparison correct port scalar _ _ _ scalarCodeBound
    (BLSResponse.good_bounded layout.response scale scaleBound)

include scaleBound addBound in
theorem bad_words (scalarCodeBound : (scalar.lower port).descriptionWords ≤ scalarWords) :
    ((badCode layout default P comparison correct port scalar scale scaleBuffers reserve add addBuffers).lower port).descriptionWords ≤
      codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
        (PairSampling.codeBudget layout.cache.value layout.cache.value scalarWords scalarWords)
        (fun signing => BLSResponse.badWords layout.response signing scaleWords addWords) :=
  code_bound (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) P comparison correct port _ _ _ _
    (PairSampling.code_bound layout.cache.value layout.cache.value layout.cache.wordFits layout.cache.pairValueFits port scalar scalar scalarCodeBound scalarCodeBound)
    (BLSResponse.bad_bounded layout.response scale add scaleBound addBound scaleBuffers (by omega) addBuffers)

variable [SampleableType (val.Value base)]
    (scalarLaw : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include scalarCorrect scalarLaw in
omit [Add G] in
theorem good_observe (signing : Bool) (tape : RandomTape w) (value : (layout.good.input default.val signing).Value) (before : State w)
    (holds : (input layout.good default).representation.Holds (request _ _ signing value) before) :
    (fun result => Subtype.val <$> Interactive.observe layout.good.output.representation result) <$>
      (goodCode layout default P comparison correct port scalar scale scaleBuffers reserve).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun rho => rho • (if signing then value.val.2.1.2 else value.val.2.1.1)) value.val.1).run
            (value.val.2.2.1, value.val.2.2.2)) :=
  observe layout.good default P comparison correct port scalar _ _ _ source scalarCorrect scalarLaw signing value tape before holds

include scalarCorrect scalarLaw in
theorem bad_observe (signing : Bool) (tape : RandomTape w) (value : (layout.bad.input (default.val, default.val) signing).Value) (before : State w)
    (holds : (input layout.bad (layout.pairDefault default)).representation.Holds (request _ _ signing value) before) :
    (fun result => Subtype.val <$> Interactive.observe layout.bad.output.representation result) <$>
      (badCode layout default P comparison correct port scalar scale scaleBuffers reserve add addBuffers).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun masks : val.Value base × val.Value base =>
            if signing then value.val.2.1.1 • (masks.1 • value.val.2.1.2.2 + masks.2 • value.val.2.1.2.1)
            else masks.1 • value.val.2.1.2.2 + masks.2 • value.val.2.1.2.1) value.val.1).run
            (value.val.2.2.1, value.val.2.2.2)) :=
  observe (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) P comparison correct port _ _ _ _
    (PairSampling.denote layout.cache.value layout.cache.value layout.cache.pairValueFits source source)
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.uniform layout.cache.value layout.cache.value layout.cache.pairValueFits source source scalarLaw scalarLaw)
    signing value tape before holds

end Signatures.Runtime.CaliperBackend.BLSDispatch
