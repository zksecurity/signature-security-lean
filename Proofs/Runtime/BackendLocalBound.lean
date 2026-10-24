import Proofs.Runtime.BackendLocalCost

/-! Compositional certificates for local backend code. The time function is
constructed from component certificates and encoded-size overhead laws. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}

structure LocalBound {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) where
  time : A → Nat
  cost_le : ∀ input, Q.cost code input ≤ time input

namespace LocalBound

/-- Keep an already implemented local operation's actual measured cost. This
does not assert that cost is small; caller trace bounds supply that obligation. -/
def measured {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) : LocalBound code where
  time := Q.cost code
  cost_le _ := le_rfl

def castFunction {A B : Type} {a : C.Str A} {b : C.Str B} {f g : A → B}
    {code : Q.Realizer a b f} (bound : LocalBound code) (h : f = g) :
    LocalBound (code.castFunction h) where
  time := bound.time
  cost_le input := by simpa using bound.cost_le input

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)

def identity {A : Type} (a : C.Str A) : LocalBound (Q.identity a) where
  time input := overhead (Q.size a input)
  cost_le := laws.identity a

def compose {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} {left : Q.Realizer a b f} {right : Q.Realizer b d g}
    (hl : LocalBound left) (hr : LocalBound right) : LocalBound (Q.compose left right) where
  time input := hl.time input + hr.time (f input) +
    overhead (Q.size a input + Q.size b (f input) + Q.size d (g (f input)))
  cost_le input := (laws.compose left right input).trans
    (Nat.add_le_add_right (Nat.add_le_add (hl.cost_le input) (hr.cost_le (f input))) _)

def fst {A B : Type} (a : C.Str A) (b : C.Str B) : LocalBound (QP.fst a b) where
  time input := overhead (Q.size (StepClass.HasProd.prod a b) input + Q.size a input.1)
  cost_le := laws.fst a b

def snd {A B : Type} (a : C.Str A) (b : C.Str B) : LocalBound (QP.snd a b) where
  time input := overhead (Q.size (StepClass.HasProd.prod a b) input + Q.size b input.2)
  cost_le := laws.snd a b

def pair {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D} {left : Q.Realizer a b f} {right : Q.Realizer a d g}
    (hl : LocalBound left) (hr : LocalBound right) : LocalBound (QP.pair left right) where
  time input := hl.time input + hr.time input +
    overhead (Q.size a input + Q.size (StepClass.HasProd.prod b d) (f input, g input))
  cost_le input := (laws.pair left right input).trans
    (Nat.add_le_add_right (Nat.add_le_add (hl.cost_le input) (hr.cost_le input)) _)

def elim {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D} {left : Q.Realizer a d f} {right : Q.Realizer b d g}
    (hl : LocalBound left) (hr : LocalBound right) : LocalBound (QS.elim left right) where
  time input := Sum.elim hl.time hr.time input +
    overhead (Q.size (StepClass.HasSum.sum a b) input + Q.size d (Sum.elim f g input))
  cost_le input := (laws.elim left right input).trans (by
    cases input with
    | inl value => exact Nat.add_le_add_right (hl.cost_le value) _
    | inr value => exact Nat.add_le_add_right (hr.cost_le value) _)

end LocalBound

namespace DataCostLaws

variable {data : DataRepresentation C} {code : DataCode Q data} {overhead : Nat → Nat}
  (laws : DataCostLaws data code overhead)

def unitBound {A : Type} (a : C.Str A) : LocalBound (code.unit a) where
  time input := overhead (Q.size a input + Q.size data.unit ())
  cost_le := laws.unit a

def boolBound (value : Bool) : LocalBound (code.bool value) where
  time input := overhead (Q.size data.unit input + Q.size data.bool value)
  cost_le := laws.bool value

def natBound (value : Nat) : LocalBound (code.nat value) where
  time input := overhead (Q.size data.unit input + Q.size data.nat value)
  cost_le := laws.nat value

def nilBound {A : Type} (a : C.Str A) : LocalBound (code.nil a) where
  time input := overhead (Q.size data.unit input + Q.size (data.list a) [])
  cost_le := laws.nil a

def consBound {A : Type} (a : C.Str A) : LocalBound (code.cons a) where
  time input := overhead (Q.size (StepClass.HasProd.prod a (data.list a)) input +
    Q.size (data.list a) (input.1 :: input.2))
  cost_le := laws.cons a

def selectBound {A : Type} (a : C.Str A) : LocalBound (code.select a) where
  time input := overhead (Q.size (StepClass.HasProd.prod data.bool a) input +
    Q.size (StepClass.HasSum.sum a a) (if input.1 = true then Sum.inl input.2 else Sum.inr input.2))
  cost_le := laws.select a

def foldBound {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    {step : A × (B × E) → B}
    {body : Q.Realizer (StepClass.HasProd.prod a (StepClass.HasProd.prod b e)) b step}
    (hb : LocalBound body) : LocalBound (code.fold a b e body) where
  time input := foldWork (fun x acc => step (x, acc, input.2.2))
    (fun x acc => hb.time (x, acc, input.2.2))
    (foldFee (Q := Q) overhead data a b e step input.2.2) input.1 input.2.1
  cost_le input := (laws.fold a b e body input).trans
    (foldWork_mono _ _ _ _ _ (fun x acc => hb.cost_le (x, acc, input.2.2))
      (fun _ _ => le_rfl) input.1 input.2.1)

end DataCostLaws

end Signatures.Runtime.BackendProgram
