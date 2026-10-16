import Signatures.Runtime.SchnorrNonzeroSigning
import Signatures.Runtime.BackendDescriptionPolynomial
import Signatures.Runtime.BackendLanguageCorrectness

/-! State-passing native code for the exact nonzero signing simulator. The
field and nonzero samplers are distinct supplied programs; both field calls and
the unconditional nonzero call contribute their complete stored descriptions. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroSigning.Native

open BackendProgram

inductive Draw : Ty CryptoAtom → Ty CryptoAtom → Type
  | field : Draw .unit scalar
  | nonzero : Draw .unit scalar

/-- Structural code outside the three sampler occurrences. -/
def description (allowance : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) : Nat :=
  Language.descriptionBound allowance primitiveSize (fun _ => 0) (body Draw.field Draw.nonzero)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S)
  (fieldDraw nonzeroDraw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
    (StepClass.HasProd.prod (rep.ty scalar) store))

def effect {a b : Ty CryptoAtom} (instr : Draw a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store) :=
  match instr with
  | .field => fieldDraw
  | .nonzero => nonzeroDraw

def semantics : SemanticsM (cryptoBase F G₁ G₂ K M) Draw (StateT S ProbComp) :=
  fun instr input saved => match instr with
  | .field => fieldDraw.denote (input, saved)
  | .nonzero => nonzeroDraw.denote (input, saved)

def code : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env Input) store)
    (StepClass.HasProd.prod (rep.ty (.pair (.pair point₁ scalar) hashCache)) store) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store
    (effect rep store fieldDraw nonzeroDraw) (body .field .nonzero)

/-- All three draws advance the actual store in order. The repair changes the
returned signature and the key programmed into the managed cache together. -/
theorem code_denote (msg : M) (g pk : G₁) (cache : List ((M × G₁) × F)) (saved : S) :
    (code rep data cost primitive store fieldDraw nonzeroDraw).denote ((msg, g, pk, cache, ()), saved) = (do
      let first ← fieldDraw.denote ((), saved)
      let second ← fieldDraw.denote ((), first.2)
      let third ← nonzeroDraw.denote ((), second.2)
      let R := second.1 • g - first.1 • pk
      let repaired := if R = 0 then (third.1 • g, second.1 + third.1) else (R, second.1)
      pure ((repaired, (cacheProgram hashEq).denote (arithmetic F G₁ G₂ K M cost)
        ((msg, repaired.1), first.1, cache, ())), third.2)) := by
  have hc := Language.compile_denote rep data (arithmetic F G₁ G₂ K M cost) primitive store
    (effect rep store fieldDraw nonzeroDraw) (semantics rep store fieldDraw nonzeroDraw)
    (fun instr input state => by cases instr <;> rfl)
    (body Draw.field Draw.nonzero) (msg, g, pk, cache, ()) saved
  rw [NonzeroSigning.body_denote] at hc
  exact hc

variable (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem code_description :
    (code rep data cost primitive store fieldDraw nonzeroDraw).descriptionSize sizes ≤
      2 * fieldDraw.descriptionSize sizes + nonzeroDraw.descriptionSize sizes +
        description allowance (fun op => sizes.localSize (primitive op)) := by
  let effectSize : {a b : Ty CryptoAtom} → Draw a b → Nat := fun instr => match instr with
    | .field => fieldDraw.descriptionSize sizes
    | .nonzero => nonzeroDraw.descriptionSize sizes
  have hc := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ K M cost) primitive dataLaws
    (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) store
    (effect rep store fieldDraw nonzeroDraw) effectSize (fun instr => by cases instr <;> exact le_rfl)
    (body Draw.field Draw.nonzero)
  apply hc.trans
  simp only [description, body, Language.descriptionBound, effectSize]
  omega

omit laws dataLaws in
/-- Polynomial original sampler and primitive descriptions imply polynomial
stored code for this fixed signing wrapper. -/
theorem codeDescription_polynomial
    (allowance : Nat → Nat) (primitiveSize : Nat → {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (fieldSize nonzeroSize : Nat → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : CryptoOp a b), PolynomiallyBounded (fun n => primitiveSize n op))
    (hField : PolynomiallyBounded fieldSize) (hNonzero : PolynomiallyBounded nonzeroSize) :
    PolynomiallyBounded (fun n => 2 * fieldSize n + nonzeroSize n + description (allowance n) (primitiveSize n)) :=
  (((PolynomiallyBounded.const 2).mul hField).add hNonzero).add
    (Language.descriptionBound_polynomial allowance primitiveSize (fun _ _ => 0)
      hAllowance hPrimitive (fun _ => PolynomiallyBounded.const 0) (body Draw.field Draw.nonzero))

end Signatures.Runtime.Schnorr.NonzeroSigning.Native
