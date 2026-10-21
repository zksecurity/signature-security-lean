import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningCoreBounds

/-! Executed frame permutations of the nonzero signing handler. After the two
replayed field draws `(c, z)` the tapes are moved in front of the retained
`((c, z), context)`, so the third (nonzero) replayed draw can run on them; its
result `(a, tapes')` is then routed into the core frame
`((a, ((c, z), g, pk, msg, managed)), (live, tapes'))`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource ByteRoute SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- Stored words of the shared replay tapes. -/
abbrev tpw : Nat := (Read.tapes config.handler.sampler.tape).representation.encoding.words
/-- Stored words of the public base `(g, pk, msg, managed)`. -/
abbrev bw : Nat := config.handler.core.base.representation.encoding.words

theorem base_words : bw config = pw config + (pw config + (mw config + tw config)) := rfl
theorem handler_width : config.handler.width = tw config + 3 * sw config + 3 * pw config + mw config + tpw config := by
  rw [Signing.Handler.Layouts.width_eq, width_eq]

theorem handler_fits {words : Nat}
    (bound : words ≤ 128 * (tw config + 3 * sw config + 3 * pw config + mw config + tpw config)) : words < 2 ^ w :=
  config.handler.fits_of_le (by rw [handler_width]; exact bound)

/-- `((c, z), context)`: the state retained across the nonzero draw. -/
def pairCtx : Representation w (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value) :=
  config.handler.core.arithmetic.scalars.representation.prod config.handler.context.representation
    (handler_fits config (by
      change (sw config + sw config) + (bw config + tw config) ≤ _
      rw [base_words]; omega))
theorem pairCtx_words : (pairCtx config).encoding.words = sw config + sw config + (bw config + tw config) := rfl

/-- `(tapes, ((c, z), context))`: input of the retained nonzero draw. -/
def middle : Representation w (PrivateSampler.Store config.handler.sampler ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) :=
  (Read.tapes config.handler.sampler.tape).representation.prod (pairCtx config)
    (handler_fits config (by
      change tpw config + (pairCtx config).encoding.words ≤ _
      rw [pairCtx_words, base_words]; omega))

/-- `((a, tapes'), ((c, z), context))`: output of the retained nonzero draw. -/
def drawn : Representation w ((Reply.scalarOutput config.handler.sampler.tape).Value ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) :=
  (Reply.scalarOutput config.handler.sampler.tape).representation.prod (pairCtx config)
    (handler_fits config (by
      change (sw config + tpw config) + _ ≤ _
      rw [pairCtx_words, base_words]; omega))

/-- `((a, input), (live, tapes'))`: input of the retained core. -/
def work : Representation w ((nzInput config).Value × config.handler.saved.Value) :=
  (nzInput config).representation.prod config.handler.saved.representation
    (handler_fits config (by
      change (nzInput config).representation.encoding.words + (tw config + tpw config) ≤ _
      rw [nzInput_words]; omega))

/-! ### Moving the tapes in front of the retained pair -/

def midValue (value : (PrivateSampler.Pair.output config.handler.sampler).Value × config.handler.context.Value) :
    PrivateSampler.Store config.handler.sampler × (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value) :=
  (⟨value.1.val.2.2, value.1.property.2.2⟩, (⟨(value.1.val.1, value.1.val.2.1), value.1.property.1, value.1.property.2.1⟩, value.2))

def midParts : List (Part w) :=
  [.slice (sw config + sw config) (tpw config), .slice 0 (sw config + sw config),
   .slice (sw config + sw config + tpw config) (bw config + tw config)]

theorem mid_valid : Valid config.handler.sampled.encoding.words (midParts config) := by
  change Valid ((sw config + (sw config + tpw config)) + (bw config + tw config)) _
  simp only [midParts, Valid]
  exact ⟨by omega, by omega, by omega, trivial⟩

theorem mid_size : words (midParts config) = (middle config).encoding.words := by
  simp only [midParts, words]
  change tpw config + (sw config + sw config + (bw config + tw config + 0)) =
    tpw config + (sw config + sw config + (bw config + tw config))
  omega

theorem mid_bytes (value : (PrivateSampler.Pair.output config.handler.sampler).Value × config.handler.context.Value) :
    bytes (config.handler.sampled.encoding.encode value) (midParts config) =
      (middle config).encoding.encode (midValue config value) := by
  let C := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let Z := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.2.1, value.1.property.2.1⟩
  let T := (Read.tapes config.handler.sampler.tape).representation.encoding.encode ⟨value.1.val.2.2, value.1.property.2.2⟩
  let X := config.handler.context.representation.encoding.encode value.2
  have hC : C.length = sw config := Encoding.encode_length _ _
  have hZ : Z.length = sw config := Encoding.encode_length _ _
  have hT : T.length = tpw config := Encoding.encode_length _ _
  have hX : X.length = bw config + tw config := Encoding.encode_length _ _
  have tapes := slice_block (C ++ Z) T X
  have pair := slice_block [] (C ++ Z) (T ++ X)
  have context := slice_block (C ++ Z ++ T) X []
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hC, hZ, hT, hX,
    List.append_assoc, ← Nat.add_assoc] at tapes pair context
  change bytes ((C ++ (Z ++ T)) ++ X) (midParts config) = T ++ ((C ++ Z) ++ X)
  simp only [midParts, bytes, List.append_nil, List.append_assoc]
  rw [tapes, pair, context]
  simp only [List.append_assoc]

def midRoute : Realizer .unit config.handler.sampled (middle config) (midValue config) :=
  ByteRoute.realizer _ _ _ (midParts config) config.sampler.wordFits (mid_valid config) (mid_size config) (mid_bytes config)

/-! ### Routing the third draw into the core frame -/

def workValue (value : (Reply.scalarOutput config.handler.sampler.tape).Value ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) :
    (nzInput config).Value × config.handler.saved.Value :=
  (⟨(value.1.val.1, (value.2.1.val, value.2.2.val.1)),
      value.1.property.1, ⟨⟨value.2.1.property, value.2.2.property.1.1⟩, value.2.2.property.1.2⟩⟩,
    ⟨(value.2.2.val.2, value.1.val.2), value.2.2.property.2, value.1.property.2⟩)

def workParts : List (Part w) :=
  [.slice 0 (sw config), .slice (sw config + tpw config) (sw config + sw config + bw config),
   .slice (sw config + tpw config + (sw config + sw config) + bw config) (tw config),
   .slice (sw config) (tpw config)]

theorem work_valid : Valid (drawn config).encoding.words (workParts config) := by
  change Valid ((sw config + tpw config) + (sw config + sw config + (bw config + tw config))) _
  simp only [workParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, trivial⟩

theorem work_size : words (workParts config) = (work config).encoding.words := by
  simp only [workParts, words]
  change sw config + (sw config + sw config + bw config + (tw config + (tpw config + 0))) =
    (sw config + ((sw config + sw config) + bw config)) + (tw config + tpw config)
  omega

theorem work_bytes (value : (Reply.scalarOutput config.handler.sampler.tape).Value ×
    (config.handler.core.arithmetic.scalars.Value × config.handler.context.Value)) :
    bytes ((drawn config).encoding.encode value) (workParts config) = (work config).encoding.encode (workValue config value) := by
  let A := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let T := (Read.tapes config.handler.sampler.tape).representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let P := config.handler.core.arithmetic.scalars.representation.encoding.encode value.2.1
  let B := config.handler.core.base.representation.encoding.encode ⟨value.2.2.val.1, value.2.2.property.1.1⟩
  let L := config.handler.core.table.representation.encoding.encode ⟨value.2.2.val.2, value.2.2.property.2⟩
  have hA : A.length = sw config := Encoding.encode_length _ _
  have hT : T.length = tpw config := Encoding.encode_length _ _
  have hP : P.length = sw config + sw config := Encoding.encode_length _ _
  have hB : B.length = bw config := Encoding.encode_length _ _
  have hL : L.length = tw config := Encoding.encode_length _ _
  have nonce := slice_block [] A (T ++ (P ++ (B ++ L)))
  have frame := slice_block (A ++ T) (P ++ B) L
  have live := slice_block (A ++ T ++ P ++ B) L []
  have tapes := slice_block A T (P ++ (B ++ L))
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hA, hT, hP, hB, hL,
    List.append_assoc, ← Nat.add_assoc] at nonce frame live tapes
  change bytes ((A ++ T) ++ (P ++ (B ++ L))) (workParts config) = (A ++ (P ++ B)) ++ (L ++ T)
  simp only [workParts, bytes, List.append_nil, List.append_assoc]
  rw [show sw config + tpw config + (sw config + sw config) + bw config =
    sw config + tpw config + sw config + sw config + bw config by omega]
  rw [nonce, live, tapes, frame]
  simp only [List.append_assoc]

def workRoute : Realizer .unit (drawn config) (work config) (workValue config) :=
  ByteRoute.realizer _ _ _ (workParts config) config.sampler.wordFits (work_valid config) (work_size config) (work_bytes config)

end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
