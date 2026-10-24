import Proofs.Runtime.Caliper.SchnorrROMReplayExtractArithmetic

/-! The executed classifier of a represented fork result. Three stored tags are
dispatched by code: the fork tag, the first pass tag and the second pass tag
(a cutoff pass is the `.inl` header). Both pass headers are projected out of the
retained frames, distributed and swapped by executed copies, and the complete
success frame is routed into the arithmetic frame. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def choiceOf (value : Unit ⊕ F) : Choice config :=
  Sum.map (fun _ => (⟨(), trivial⟩ : config.handler.sampler.tape.unit.Value))
    (fun scalar => (⟨scalar, trivial⟩ : config.handler.sampler.tape.scalar.Value)) value

theorem choiceView_eq (value : Unit ⊕ F) (valid : (choiceLayout config).valid value) :
    choiceView config ⟨value, valid⟩ = choiceOf config value := by
  cases value <;> rfl

section Classify
variable [DecidableEq F] [DecidableEq G] [Sub F] [Div F] (arith : Arithmetic config)

/-- The source classification: `.inr` exactly for a successful fork whose two
passes both returned forgeries, with equal commitments and distinct challenges. -/
def classifyValue (value : Result config) : Unit ⊕ F :=
  match value with
  | .inl _ => .inl ()
  | .inr pair =>
    match pair.1.1, pair.2.1 with
    | .inr first, .inr second => coreValue (quadOf config first second)
    | _, _ => .inl ()
def classifyChoice (value : Result config) : Choice config := choiceOf config (classifyValue config value)

def coreChoice (value : (quad config).Value) : Choice config :=
  choiceView config ⟨coreValue value.val, (core config arith).preserves value.val value.property⟩
def coreRealizer : Realizer .unit (quad config).representation (choice config) (coreChoice config arith) :=
  (core config arith).program.viewOutput (choice config) (coreChoice config arith) (fun _ => rfl)

def forged : Realizer .unit (forgedPair config) (choice config) (coreChoice config arith ∘ gatherValue config) :=
  (gather config).then (coreRealizer config arith)
def secondBranch := branchRealizer .unit (by decide)
  ((Pairing.unitRepresentation w).prod (ForgeryHash.result config) (by have := second_fits config; omega))
  (forgedPair config) (choice config) (fallback config _) (forged config arith) config.sampler.wordFits
  (by have := second_fits config; change 1 + max (0 + _) (_ + _) < _; change 1 + max 0 _ + _ < _ at this; omega)
def afterFirst := (swapFrame config).then ((distributeSecond config).then (secondBranch config arith))
def firstBranch := branchRealizer .unit (by decide)
  ((Pairing.unitRepresentation w).prod (header config) (by have := frame_fits config; omega))
  ((ForgeryHash.result config).prod (header config) (by have := frame_fits config; omega))
  (choice config) (fallback config _) (afterFirst config arith) config.sampler.wordFits
  (by have := frame_fits config; change 1 + max (0 + _) (_ + _) < _; change 1 + max 0 _ + _ < _ at this; omega)
def passes := (headersRoute config).then ((distributeFirst config).then (firstBranch config arith))
def dispatched := branchRealizer .unit (by decide) (Pairing.unitRepresentation w) (pair config) (choice config)
  (fallback config _) (passes config arith) config.sampler.wordFits (output config).fits

theorem dispatched_value (value : Result config) :
    (choice config).encoding.encode (classifyChoice config value) =
      (choice config).encoding.encode (Sum.elim (fun _ => fallbackValue config)
        ((fun middle => Sum.elim (fun _ => fallbackValue config)
          ((fun framed => Sum.elim (fun _ => fallbackValue config) (coreChoice config arith ∘ gatherValue config)
            (SumContext.view framed)) ∘ Prod.swap) middle) ∘ SumContext.view ∘ headersValue config) value) := by
  apply congrArg
  rcases value with _ | ⟨⟨first, firstStore⟩, ⟨second, secondStore⟩⟩
  · rfl
  · rcases first with _ | first <;> rcases second with _ | second
    · rfl
    · rfl
    · rfl
    · exact (choiceView_eq config _ _).symm

/-- The complete executed classifier on the controller's represented result. -/
def classifier : Realizer .unit (output config) (choice config) (classifyChoice config) :=
  (dispatched config arith).viewOutput (choice config) (classifyChoice config) (dispatched_value config arith)

end Classify
end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork.Extract
