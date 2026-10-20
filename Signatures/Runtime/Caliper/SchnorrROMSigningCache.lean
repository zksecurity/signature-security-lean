import Signatures.Runtime.Caliper.SchnorrROMSigningArithmetic

/-! The managed cache update is the constructed finite-list programmer. Hits
preserve the stored answer, including zero; misses prepend the new challenge.
The signature and public configuration are retained by executed copying. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Cache
open Caliper BoundedSource

abbrev keyTy : Ty CryptoAtom := .pair message point₁
inductive Comparison : Ty CryptoAtom → Ty CryptoAtom → Type
  | equal : Comparison (.pair keyTy keyTy) .bool
def primitives (F G M : Type) [DecidableEq M] [DecidableEq G] : Primitives (cryptoBase F G Unit M M) Comparison where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
def comparison : Expr Comparison [keyTy, keyTy] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
theorem comparison_correct (F G M : Type) [DecidableEq M] [DecidableEq G] (left right : M × G) :
    comparison.denote (primitives F G M) (left, right, ()) = decide (left = right) := rfl

variable {w : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G] (layout : Layouts w M F G)

def update (input : CacheLayout.Input (M × G) F) : Table M F G :=
  if (lookupValue input.1 input.2.1 input.2.2.1).1 = true then input.2.2.1 else (input.1, input.2.1) :: input.2.2.1

theorem update_eq : (cacheProgram (val := scalar) comparison).denote (primitives F G M) = update := by
  funext input
  rcases input with ⟨key, challenge, table, ⟨⟩⟩
  simpa only [Expr.run_value, update] using cacheProgram_value (val := scalar) (primitives F G M) comparison
    (comparison_correct F G M) key challenge table

def programmer : Implementation .unit layout.cache.input layout.table update :=
  (EncodedCache.implementation (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar)
    layout.cache (primitives F G M) comparison (comparison_correct F G M)).castFunction update_eq
theorem programmer_buffers : (programmer layout).program.code.memBound ≤ 8 :=
  EncodedCache.buffers (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar)
    layout.cache (primitives F G M) comparison (comparison_correct F G M)
theorem programmer_nameFits : (programmer layout).program.savedBuffer < 2 ^ w := by
  have bounded := programmer_buffers layout
  have := layout.wordFits
  change max 2 (programmer layout).program.code.memBound < _
  omega

def finishValue (value : layout.table.Value × layout.saved.Value) : layout.output.Value :=
  ⟨(value.2.val.1, value.2.val.2, value.1.val), value.2.property.1, value.2.property.2, value.1.property⟩
def finish : Realizer .unit layout.programmed layout.output.representation (finishValue layout) :=
  (Pairing.swap .unit (by decide) layout.table.representation layout.saved.representation layout.wordFits layout.programmed.fits).viewOutput
    layout.output.representation (finishValue layout) (by
      intro value
      change _ ++ (_ ++ _) = (_ ++ _) ++ _
      exact (List.append_assoc _ _ _).symm)

def retained : Realizer .unit layout.work.representation layout.programmed
    (fun value => (⟨update value.val.1, (programmer layout).preserves value.val.1 value.property.1⟩,
      ⟨value.val.2, value.property.2⟩)) :=
  ((programmer layout).program.retain (by decide) layout.saved.representation layout.wordFits (programmer_nameFits layout)
    layout.work.representation.fits layout.programmed.fits).viewInput layout.work.representation
      (productView layout.cache.input layout.saved) (fun _ => rfl)

def value (input : CacheLayout.Input (M × G) F × Saved F G) : Output M F G :=
  (input.2.1, input.2.2, update input.1)
def implementation : Implementation .unit layout.work layout.output value where
  preserves _ valid := ⟨valid.2.1, valid.2.2, (programmer layout).preserves _ valid.1⟩
  program := (retained layout).then (finish layout)

def lookupTime := EncodedCache.timeBudget (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar) layout.cache
def lookupWords := EncodedCache.codeBudget (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar) layout.cache
def timeBudget := lookupTime layout + 48 * layout.width
def codeBudget := lookupWords layout + 150 * layout.width + 60

theorem programmer_bounded : (programmer layout).BoundedBy (lookupTime layout) (lookupWords layout) :=
  (EncodedCache.bounded (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar)
    layout.cache (primitives F G M) comparison (comparison_correct F G M)).castFunction update_eq

theorem sizes : layout.cache.input.representation.encoding.words ≤ layout.width ∧
    layout.table.representation.encoding.words ≤ layout.width ∧ layout.saved.representation.encoding.words ≤ layout.width := by
  change layout.cache.lookup.input.representation.encoding.words ≤ _ ∧ _ ∧ _
  rw [LookupLayout.input_words, Layouts.table_words]
  change (1 + (layout.capacityPred + 1) * (layout.message.representation.encoding.words + layout.point.representation.encoding.words +
    layout.scalar.representation.encoding.words) + (layout.message.representation.encoding.words + layout.point.representation.encoding.words) +
    layout.scalar.representation.encoding.words) ≤ _ ∧ _ ∧
    (layout.point.representation.encoding.words + layout.scalar.representation.encoding.words) +
      (layout.point.representation.encoding.words + layout.point.representation.encoding.words) ≤ _
  unfold Layouts.width
  exact ⟨by omega, by omega, by omega⟩

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have computed := programmer_bounded layout
  have copiedTime := (programmer layout).program.retain_time_unit_le layout.saved.representation layout.wordFits
    (programmer_nameFits layout) layout.work.representation.fits layout.programmed.fits
  have copiedWords := (programmer layout).program.retain_descriptionWords_le (by decide) layout.saved.representation layout.wordFits
    (programmer_nameFits layout) layout.work.representation.fits layout.programmed.fits
  have swappedWords := Pairing.swap_descriptionWords_le .unit (by decide) layout.table.representation layout.saved.representation
    layout.wordFits layout.programmed.fits
  have sizes := sizes layout
  constructor
  · intro input
    have elapsed := computed.time_le ⟨input.val.1, input.property.1⟩
    have copied := copiedTime (productView layout.cache.input layout.saved input)
    have swapped := Pairing.swap_time_unit_le layout.table.representation layout.saved.representation layout.wordFits layout.programmed.fits
      (⟨update input.val.1, (programmer layout).preserves input.val.1 input.property.1⟩, ⟨input.val.2, input.property.2⟩)
    change (retained layout).time input ≤ _ at copied
    change (finish layout).time
      (⟨update input.val.1, (programmer layout).preserves input.val.1 input.property.1⟩, ⟨input.val.2, input.property.2⟩) ≤ _ at swapped
    change (retained layout).time input + (finish layout).time
      (⟨update input.val.1, (programmer layout).preserves input.val.1 input.property.1⟩, ⟨input.val.2, input.property.2⟩) ≤ _
    change (retained layout).time input ≤ (programmer layout).program.time ⟨input.val.1, input.property.1⟩ +
      8 * layout.cache.input.representation.encoding.words + 8 * layout.table.representation.encoding.words +
      12 * layout.saved.representation.encoding.words at copied
    unfold timeBudget
    omega
  · have stored := computed.code_le
    change descriptionWords (retained layout).code ≤ _ at copiedWords
    change descriptionWords (finish layout).code ≤ _ at swappedWords
    change descriptionWords (_ ;; _) ≤ _
    rw [descriptionWords_seq]
    unfold codeBudget
    omega

theorem buffers : (implementation layout).program.code.memBound ≤ 9 := by
  have computed := programmer_buffers layout
  have held := (programmer layout).program.retain_buffers (by decide) layout.saved.representation layout.wordFits
    (programmer_nameFits layout) layout.work.representation.fits layout.programmed.fits
  have swapped := Reorder.buffers (w := w) layout.table.representation.encoding.words layout.saved.representation.encoding.words 0
  change (retained layout).code.memBound ≤ _ at held
  change (finish layout).code.memBound ≤ 2 at swapped
  change max (retained layout).code.memBound (finish layout).code.memBound ≤ _
  omega

theorem names : NamesAccounted (implementation layout).program.code 5 :=
  (Retain.names (EncodedCache.names (base := cryptoBase F G Unit M M) (key := keyTy) (val := scalar)
    layout.cache (primitives F G M) comparison (comparison_correct F G M)) _ _ _).seq (Reorder.names _ _ _ _)

theorem length (input : CacheLayout.Input (M × G) F) : (update input).length ≤ input.2.2.1.length + 1 := by
  unfold update
  split <;> simp

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Cache
