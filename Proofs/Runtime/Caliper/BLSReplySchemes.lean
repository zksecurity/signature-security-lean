import Proofs.Runtime.Caliper.BLSReplyMemory
import Proofs.Runtime.Caliper.BLSResponseMemory
import Proofs.Runtime.Caliper.BLSCachePairs

/-! Both BLS AGM replies assembled from scalar sampling, scalar multiplication
and addition. No implementation or efficiency premise for a finished reply is
supplied. Public challenge points and the signing scalar are stored input data. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply
open Caliper BoundedSource OracleComp OracleSpec

structure SchemeLayouts (w : Nat) (M F G : Type) where
  cache : CacheLayout w M F
  point : Layout w G
  responseFits : 16 * (cache.value.representation.encoding.words + point.representation.encoding.words) < 2 ^ w
  capacityPred : Nat
  countFits : capacityPred + 1 < 2 ^ w
  goodFits : 16 * (cache.lookup.width + 3 * point.representation.encoding.words +
    2 * (1 + (capacityPred + 1) * (cache.key.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w
  pairFits : cache.pairStorageWords < 2 ^ w
  badFits : 16 * ((cache.pairValues pairFits).lookup.width + cache.value.representation.encoding.words +
    3 * point.representation.encoding.words +
    2 * (1 + (capacityPred + 1) * (cache.key.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace SchemeLayouts
variable {w : Nat} {M F G : Type} (layout : SchemeLayouts w M F G)

def response : BLSResponse.Layouts w F G := ⟨layout.cache.value, layout.point, layout.cache.wordFits, layout.responseFits⟩

def good : Layouts w M F (G × G) G where
  cache := layout.cache
  point := layout.point
  config := layout.response.points
  capacityPred := layout.capacityPred
  countFits := layout.countFits
  storageFits := by
    have h := layout.goodFits
    change 16 * (layout.cache.lookup.width + (layout.point.representation.encoding.words + layout.point.representation.encoding.words) +
      layout.point.representation.encoding.words + 2 * (1 + (layout.capacityPred + 1) *
        (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words))) < 2 ^ w
    omega

def bad : Layouts w M (F × F) (F × (G × G)) G where
  cache := layout.cache.pairValues layout.pairFits
  point := layout.point
  config := layout.response.config
  capacityPred := layout.capacityPred
  countFits := layout.countFits
  storageFits := by
    have h := layout.badFits
    change 16 * ((layout.cache.pairValues layout.pairFits).lookup.width +
      (layout.cache.value.representation.encoding.words + (layout.point.representation.encoding.words + layout.point.representation.encoding.words)) +
      layout.point.representation.encoding.words + 2 * (1 + (layout.capacityPred + 1) *
        (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words))) < 2 ^ w
    omega

def pairDefault (default : layout.cache.value.Value) : layout.bad.cache.value.Value :=
  ⟨(default.val, default.val), default.property, default.property⟩

include layout in
theorem goodReserve {slots : Nat} (reserve : slots + 5 < 2 ^ w) : max 3 slots + 3 < 2 ^ w := by
  have h := layout.cache.wordFits
  omega

include layout in
theorem badReserve {slots : Nat} (reserve : slots + 5 < 2 ^ w) : (max 3 slots + 2) + 3 < 2 ^ w := by
  have h := layout.cache.wordFits
  omega
end SchemeLayouts

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G : Type}
    [DecidableEq (key.Value base)] [SMul (val.Value base) G]
    (layout : SchemeLayouts w (key.Value base) (val.Value base) G)
    (default : layout.cache.value.Value) (signing : Bool)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (scalar : Interactive.Code w)
    (scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 5 < 2 ^ w)

def goodCode : Interactive.Code w :=
  code layout.good default signing P comparison correct port scalar (BLSResponse.good layout.response scale signing)
    (BLSResponse.good_buffers layout.response scale scaleBuffers signing) (layout.goodReserve reserve)

variable [Add G] (add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2))
    (addBuffers : add.program.code.memBound ≤ slots)

def badCode : Interactive.Code w :=
  code (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) signing P comparison correct port
    (BLSCache.pairSampler layout.cache port scalar)
    (BLSResponse.bad layout.response scale add scaleBuffers (by omega) addBuffers signing)
    (BLSResponse.bad_buffers layout.response scale add scaleBuffers (by omega) addBuffers signing) (layout.badReserve reserve)

variable {source : ProbComp layout.cache.value.Value}
    (scalarCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation layout.cache.value.representation (fun _ => source) scalar)
    {scalarTime scalarWords scaleTime scaleWords addTime addWords : Nat}
    (scalarBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation scalar scalarTime)
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (addBound : add.BoundedBy addTime addWords)

include scalarCorrect scalarBound scaleBound in
omit [Add G] in
theorem good_time : Interactive.TimeBound port .unit (layout.good.input default.val signing).representation
    (goodCode layout default signing P comparison correct port scalar scale scaleBuffers reserve)
    (timeBudget layout.good scalarTime (BLSResponse.goodTime layout.response scaleTime)) :=
  time_bound layout.good default signing P comparison correct port scalar scalarCorrect scalarBound _ _ _
    (BLSResponse.good_bounded layout.response scale scaleBound signing)

include scalarCorrect scalarBound scaleBound addBound in
theorem bad_time : Interactive.TimeBound port .unit (layout.bad.input (default.val, default.val) signing).representation
    (badCode layout default signing P comparison correct port scalar scale scaleBuffers reserve add addBuffers)
    (timeBudget (base := base) (key := key) (val := .pair val val) layout.bad
      (PairSampling.timeBudget layout.cache.value layout.cache.value scalarTime scalarTime)
      (BLSResponse.badTime layout.response signing scaleTime addTime)) :=
  time_bound (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) signing P comparison correct port _
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect scalarBound scalarBound) _ _ _
    (BLSResponse.bad_bounded layout.response scale add scaleBound addBound scaleBuffers (by omega) addBuffers signing)

include scaleBound in
omit [Add G] in
theorem good_words (scalarCodeBound : (scalar.lower port).descriptionWords ≤ scalarWords) :
    ((goodCode layout default signing P comparison correct port scalar scale scaleBuffers reserve).lower port).descriptionWords ≤
      codeBudget layout.good scalarWords (BLSResponse.goodWords layout.response scaleWords) :=
  code_bound layout.good default signing P comparison correct port scalar scalarCodeBound _ _ _
    (BLSResponse.good_bounded layout.response scale scaleBound signing)

include scaleBound addBound in
theorem bad_words (scalarCodeBound : (scalar.lower port).descriptionWords ≤ scalarWords) :
    ((badCode layout default signing P comparison correct port scalar scale scaleBuffers reserve add addBuffers).lower port).descriptionWords ≤
      codeBudget (base := base) (key := key) (val := .pair val val) layout.bad
        (PairSampling.codeBudget layout.cache.value layout.cache.value scalarWords scalarWords)
        (BLSResponse.badWords layout.response signing scaleWords addWords) :=
  code_bound (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) signing P comparison correct port _
    (PairSampling.code_bound layout.cache.value layout.cache.value layout.cache.wordFits layout.cache.pairValueFits port scalar scalar scalarCodeBound scalarCodeBound) _ _ _
    (BLSResponse.bad_bounded layout.response scale add scaleBound addBound scaleBuffers (by omega) addBuffers signing)

variable [SampleableType (val.Value base)]
    (scalarLaw : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include scalarCorrect scalarLaw in
omit [Add G] in
theorem good_observe (tape : RandomTape w) (value : (layout.good.input default.val signing).Value) (before : State w)
    (holds : (layout.good.input default.val signing).representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.good.output.representation result) <$>
      (goodCode layout default signing P comparison correct port scalar scale scaleBuffers reserve).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun rho => rho • (if signing then value.val.2.1.2 else value.val.2.1.1)) value.val.1).run
            (value.val.2.2.1, value.val.2.2.2)) :=
  observe layout.good default signing P comparison correct port scalar _ _ _ source scalarCorrect scalarLaw tape value before holds

include scalarCorrect scalarLaw in
theorem bad_observe (tape : RandomTape w) (value : (layout.bad.input (default.val, default.val) signing).Value) (before : State w)
    (holds : (layout.bad.input (default.val, default.val) signing).representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe layout.bad.output.representation result) <$>
      (badCode layout default signing P comparison correct port scalar scale scaleBuffers reserve add addBuffers).execute port .unit tape before =
        some <$> ((fun out => (out.1, value.val.2.1, out.2)) <$>
          (LazyAGM.listReply signing (fun masks : val.Value base × val.Value base =>
            if signing then value.val.2.1.1 • (masks.1 • value.val.2.1.2.2 + masks.2 • value.val.2.1.2.1)
            else masks.1 • value.val.2.1.2.2 + masks.2 • value.val.2.1.2.1) value.val.1).run
            (value.val.2.2.1, value.val.2.2.2)) :=
  observe (base := base) (key := key) (val := .pair val val) layout.bad (layout.pairDefault default) signing P comparison correct port _ _ _ _
    (PairSampling.denote layout.cache.value layout.cache.value layout.cache.pairValueFits source source)
    (PairSampling.refines (hw := layout.cache.wordFits) (fits := layout.cache.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.uniform layout.cache.value layout.cache.value layout.cache.pairValueFits source source scalarLaw scalarLaw)
    tape value before holds

end Signatures.Runtime.CaliperBackend.BLSReply
