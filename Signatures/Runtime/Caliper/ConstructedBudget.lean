import Signatures.Runtime.Caliper.Constructed

/-! Budget equations expose composition without normalizing the implementation
and correctness proofs of its components. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
variable {w : Nat} {A B D : Type} {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D}

theorem pair_budget (first : Constructed input left f) (second : Constructed input right g)
    (hw : 16 < 2 ^ w) (firstFits : first.buffers < 2 ^ w) (secondFits : second.buffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (first.pair second hw firstFits secondFits duplicateFits middleFits outputFits).budget =
      Budget.pair input.representation.encoding.words left.representation.encoding.words right.representation.encoding.words
        first.budget second.budget := rfl

end Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
