import Signatures.Runtime.Caliper.LookupLayout
import Signatures.Runtime.Caliper.EncodedEquality
import Signatures.Runtime.Lookup

/-! Compilation of the original association-list lookup expression. Only key
comparison is supplied; projections, Boolean branches, the found/value state,
and the complete bounded table traversal are constructed from existing code. -/

namespace Signatures.Runtime.CaliperBackend.SourceLookup

open Caliper BoundedSource SourceExpression

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    (P : Primitives base Op) {key val : Ty Atom} (eq : Op (.pair key key) .bool)
    (layout : LookupLayout w (key.Value base) (val.Value base))

abbrev Context (key val : Ty Atom) := [key, val, .list (.pair key val)]
abbrev BodyContext (key val : Ty Atom) := [.pair key val, .pair .bool val, key, val, .list (.pair key val)]

def entryCode : Compilation P .unit layout.wordFits
    (.var .here : Expr Op (BodyContext key val) (.pair key val)) layout.body layout.entry := by
  refine Compilation.var (P := P) (hw := layout.wordFits)
    (Variable.here (base := base) (Γ := [.pair .bool val, key, val, .list (.pair key val)]) (a := .pair key val) layout.entry layout.accumulatorTail ?_)
  have bound := layout.argumentFits
  change _ + (_ + _) < _
  omega

def accumulatorCode : Compilation P .unit layout.wordFits
    (.var (.there .here) : Expr Op (BodyContext key val) (.pair .bool val)) layout.body layout.result := by
  refine Compilation.var (P := P) (hw := layout.wordFits)
    (Variable.there (base := base) (b := .pair key val) layout.entry
      (Variable.here (base := base) (Γ := Context key val) (a := .pair .bool val) layout.result layout.input ?_) ?_)
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

def keyCode : Compilation P .unit layout.wordFits
    (.var (.there (.there .here)) : Expr Op (BodyContext key val) key) layout.body layout.key := by
  refine Compilation.var (P := P) (hw := layout.wordFits)
    (Variable.there (base := base) (b := .pair key val) layout.entry
      (Variable.there (base := base) (b := .pair .bool val) layout.result
        (Variable.here (base := base) (Γ := [val, .list (.pair key val)]) (a := key) layout.key layout.valueTail ?_) ?_) ?_)
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

def defaultCode : Compilation P .unit layout.wordFits
    (.var (.there .here) : Expr Op (Context key val) val) layout.input layout.value := by
  refine Compilation.var (P := P) (hw := layout.wordFits)
    (Variable.there (base := base) (b := key) layout.key
      (Variable.here (base := base) (Γ := [.list (.pair key val)]) (a := val) layout.value layout.tableTail ?_) ?_)
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

def tableCode : Compilation P .unit layout.wordFits
    (.var (.there (.there .here)) : Expr Op (Context key val) (.list (.pair key val))) layout.input layout.table := by
  refine Compilation.var (P := P) (hw := layout.wordFits)
    (Variable.there (base := base) (b := key) layout.key
      (Variable.there (base := base) (b := val) layout.value
        (Variable.here (base := base) (Γ := []) (a := .list (.pair key val)) layout.table layout.unit ?_) ?_) ?_)
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

variable (comparison : Implementation .unit (layout.key.prod layout.key layout.keyPairFits)
    layout.boolean (P.execute eq))

def testCode : Compilation P .unit layout.wordFits
    (.op eq (.pair (.fst (.var .here)) (.var (.there (.there .here)))) : Expr Op (BodyContext key val) .bool)
    layout.body layout.boolean := by
  refine .op eq comparison (.pair (Compilation.fst (a := key) (b := val) layout.key layout.value ?_ (entryCode P layout)) (keyCode P layout) layout.body_duplicateFits ?_ layout.keyPairFits)
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

def foundCode : Compilation P .unit layout.wordFits
    (.pair (.bool true) (.snd (.var .here)) : Expr Op (BodyContext key val) (.pair .bool val))
    layout.body layout.result := by
  refine .pair (Compilation.bool (w := w) (P := P) (cost := .unit) (hw := layout.wordFits) (Γ := BodyContext key val) layout.body true) (Compilation.snd (a := key) (b := val) layout.key layout.value ?_ (entryCode P layout))
    layout.body_duplicateFits layout.body_tagFits ?_
  all_goals
    apply layout.fits_of_le
    dsimp [LookupLayout.width]
    omega

def bodyCode : Compilation P .unit layout.wordFits (lookupBody eq) layout.body layout.result := by
  refine .branch (Compilation.fst (a := .bool) (b := val) layout.boolean layout.value ?_ (accumulatorCode P layout)) (accumulatorCode P layout)
    (.branch (testCode P eq layout comparison) (foundCode P layout) (accumulatorCode P layout)
      layout.body_duplicateFits layout.body_tagFits) layout.body_duplicateFits layout.body_tagFits
  all_goals
    apply layout.fits_of_le
    try simp
    dsimp [LookupLayout.width]
    omega

def initialCode : Compilation P .unit layout.wordFits
    (.pair (.bool false) (.var (.there .here)) : Expr Op (Context key val) (.pair .bool val))
    layout.input layout.result := by
  refine .pair (Compilation.bool (w := w) (P := P) (cost := .unit) (hw := layout.wordFits) (Γ := Context key val) layout.input false) (defaultCode P layout)
    layout.input_duplicateFits layout.input_booleanFits ?_

/-- A certificate for the same `lookup eq` used by the source reductions. -/
def certificate : Compilation P .unit layout.wordFits (lookup eq) layout.input layout.result :=
  Compilation.fold (w := w) (P := P) (cost := .unit) (hw := layout.wordFits)
    (Γ := Context key val) (a := .pair key val) (b := .pair .bool val) layout.input layout.entry layout.result layout.capacity layout.countFits layout.argumentFits layout.frameFits
    (tableCode P layout) (initialCode P layout) (bodyCode P eq layout comparison)

def localBounds (budget : comparison.Budget) : (certificate P eq layout comparison).LocalBounds :=
  ((), ((), ()), ((), (), ((((), ()), budget), ((), ()), ())))

theorem primitiveNames {slots : Nat} (names : NamesBound comparison.program.code slots) :
    (certificate P eq layout comparison).PrimitiveNames slots :=
  ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial, ⟨⟨⟨trivial, trivial⟩, names⟩, ⟨trivial, trivial⟩, trivial⟩⟩⟩

/-- An encoded comparator implements the designated source equality instruction.
The semantic equality equation is proved at the primitive boundary. -/
def encodedComparison [DecidableEq (key.Value base)]
    (correct : ∀ left right, P.execute eq (left, right) = decide (left = right)) :
    Implementation .unit (layout.key.prod layout.key layout.keyPairFits) layout.boolean (P.execute eq) :=
  (EncodedEquality.implementation .unit layout.key layout.wordFits layout.keyPairFits).castFunction
    (by funext value; exact (correct value.1 value.2).symm)

def encodedBudget [DecidableEq (key.Value base)]
    (correct : ∀ left right, P.execute eq (left, right) = decide (left = right)) :
    (encodedComparison P eq layout correct).Budget where
  estimate := ⟨6 * layout.key.representation.encoding.words + 3, 30 * layout.key.representation.encoding.words + 13⟩
  bounded := ⟨fun _ => (EncodedEquality.time_unit _).le, (EncodedEquality.code_descriptionWords _).le⟩

theorem encodedNames [DecidableEq (key.Value base)]
    (correct : ∀ left right, P.execute eq (left, right) = decide (left = right)) :
    NamesBound (encodedComparison P eq layout correct).program.code 5 := EncodedEquality.code_names _

theorem source_value [DecidableEq (key.Value base)]
    (correct : ∀ left right, P.execute eq (left, right) = decide (left = right))
    (value : Env base (Context key val)) :
    (lookup eq).denote P value = lookupValue value.1 value.2.1 value.2.2.1 := by
  simpa only [Expr.run_value] using lookup_correct P eq correct value.1 value.2.1 value.2.2.1

end Signatures.Runtime.CaliperBackend.SourceLookup
