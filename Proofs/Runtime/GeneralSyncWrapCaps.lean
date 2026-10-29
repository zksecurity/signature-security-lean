import Proofs.Runtime.GeneralSyncWrapRealizer
import Proofs.Runtime.BackendCallerCost
import Proofs.Runtime.BackendCallerDescription
import Proofs.Runtime.BackendWeightedHandlerBudget
import Proofs.Runtime.BackendWeightedSolverContracts
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.BackendListLength

/-! # Backend contracts and size facts for the wrapper

The wrapper's codes use, beyond the structural operations the weighted pipeline already prices,
the optional-value `map` and `bindContext` wiring, the five adapters of `WrapPorts`, and the
scheme's three routines. Their costs and descriptions are contracted here in the same style as
the pipeline's `DispatchCostLaws` and port caps: nothing about a completed solver is assumed.
The size facts bound every value the wrapper holds: marks, states, readouts and tagged replies. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]

/-! ## Optional-value wiring laws -/

/-- Costs of the optional-value wiring: mapping or binding charges the inner code on a present
value plus structural overhead at the encoded sizes. -/
structure OptionCostLaws (overhead : Nat → Nat) : Prop where
  map : ∀ {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B} (code : Q.Realizer a b f) (input : Option A),
    Q.cost (QO.map code) input ≤ (match input with | none => 0 | some value => Q.cost code value) +
      overhead (Q.size (StepClass.HasOption.option a) input + Q.size (StepClass.HasOption.option b) (input.map f))
  bindContext : ∀ {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E} {k : A × E → Option B}
    (code : Q.Realizer (StepClass.HasProd.prod a e) (StepClass.HasOption.option b) k) (input : Option A × E),
    Q.cost (QO.bindContext code) input ≤
      (match input.1 with | none => 0 | some value => Q.cost code (value, input.2)) +
        overhead (Q.size (StepClass.HasProd.prod (StepClass.HasOption.option a) e) input +
          Q.size (StepClass.HasOption.option b) (input.1.bind fun value => k (value, input.2)))

/-- Descriptions of the optional-value wiring. -/
structure OptionDescriptionLaws (sizes : DescriptionSize Q) (allowance : Nat) : Prop where
  map : ∀ {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B} (code : Q.Realizer a b f),
    sizes.localSize (QO.map code) ≤ sizes.localSize code + allowance
  bindContext : ∀ {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E} {k : A × E → Option B}
    (code : Q.Realizer (StepClass.HasProd.prod a e) (StepClass.HasOption.option b) k),
    sizes.localSize (QO.bindContext code) ≤ sizes.localSize code + allowance

variable {F G₁ G₂ K M : Type} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI)
  (wports : WrapPorts rep ports)
  (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂)
  (code : SchemeCode rep correction finalFn keys)

attribute [local implicit_reducible] PFunctor.Idx

/-! ## Adapter and routine contracts -/

/-- Size and cost caps of the wrapper's adapters. `routeWidth` bounds the attacker's encoded
outputs, `outputWidth` their decoding, `finishedWidth` the decoded finished output and
`finishedRoute` its encoding. -/
structure WrapPortCaps (width routeWidth outputWidth finishedWidth finishedRoute adapterTime : Nat) : Prop where
  input : ∀ pk : G₂ × G₂, Q.size (rep.ty (.pair point₂ point₂)) pk ≤ 3 * width →
    Q.size bdI.input pk ≤ routeWidth ∧ Q.cost wports.input pk ≤ adapterTime
  output : ∀ out, Q.size bdI.out out ≤ routeWidth →
    Q.size (rep.ty OutTy) out ≤ outputWidth ∧ Q.cost wports.output out ≤ adapterTime
  encode : ∀ out, Q.size (rep.ty OutTy) out ≤ finishedWidth →
    Q.size bdI.out out ≤ finishedRoute ∧ Q.cost wports.encode out ≤ adapterTime
  position : ∀ p, Q.size (posRep rep) p ≤ 3 * width →
    Q.size bdI.pos p ≤ 8 * width ∧ Q.cost wports.position p ≤ adapterTime
  reply : ∀ idx, Q.size bdI.idx idx ≤ 8 * width →
    Q.size (replyRep rep ports) (decodeIdx F G₁ G₂ K M randomBound idx) ≤ 8 * width ∧ Q.cost wports.reply idx ≤ adapterTime

/-- Descriptions of the wrapper's adapters. -/
structure WrapPortDescriptions (sizes : DescriptionSize Q) (portSize : Nat) : Prop where
  input : sizes.localSize wports.input ≤ portSize
  output : sizes.localSize wports.output ≤ portSize
  encode : sizes.localSize wports.encode ≤ portSize
  position : sizes.localSize wports.position ≤ portSize
  reply : sizes.localSize wports.reply ≤ portSize

/-- Cost caps of the scheme's routines on bounded inputs. -/
structure SchemeCaps (width routineTime : Nat) : Prop where
  corr : ∀ m : K × F, Q.size (rep.ty Weights.syncMessage) m ≤ 3 * width → Q.cost code.corr m ≤ routineTime
  fin : ∀ m : K × F, Q.size (rep.ty Weights.syncMessage) m ≤ 3 * width → Q.cost code.fin m ≤ routineTime
  keys : ∀ pk : G₂, Q.size (rep.ty point₂) pk ≤ width →
    Q.size (rep.ty (.pair point₂ point₂)) (keys pk) ≤ 3 * width ∧ Q.cost code.keys pk ≤ routineTime

/-- Descriptions of the scheme's routines. -/
structure SchemeDescriptions (sizes : DescriptionSize Q) (routineSize : Nat) : Prop where
  corr : sizes.localSize code.corr ≤ routineSize
  fin : sizes.localSize code.fin ≤ routineSize
  keys : sizes.localSize code.keys ≤ routineSize

/-! ## Sizes -/

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (R : GeneralCaller.Caller (Q := Q) (bd := bdI))

local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum

/-- Encoded width of a mark list of bounded length. -/
def marksWidth (width cap : Nat) : Nat := (4 * cap + 1) * width

include sizes lists in
theorem mark_size (width : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (m : Mark F) : Q.size (rep.ty markTy) m ≤ 3 * width := by
  have h := sizes.prod_le rep.data.bool (rep.ty scalar) m
  have h1 := hb m.1
  have h2 := hf m.2
  change Q.size (rep.ty markTy) m ≤ _ at h
  omega

include sizes lists in
theorem marks_size (width cap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (marks : List (Mark F)) (hl : marks.length ≤ cap) :
    Q.size (marksRep rep) marks ≤ marksWidth width cap := by
  have h := lists.size_le_cap (rep.ty markTy) marks (3 * width) cap
    (fun m _ => mark_size rep sizes lists width hh hb hf m) hl
  change Q.size (marksRep rep) marks ≤ _ at h
  have hc := Nat.mul_le_mul_left cap hh
  dsimp only [marksWidth]
  nlinarith

include sizes in
theorem ready_size (width cap stateWidth : Nat) (hh : header ≤ width)
    (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hm : Q.size (marksRep rep) marks ≤ marksWidth width cap) :
    Q.size (readyRep rep R) (s, marks) ≤ stateWidth + marksWidth width cap + width := by
  have h := sizes.prod_le R.state (marksRep rep) (s, marks)
  change Q.size (readyRep rep R) (s, marks) ≤ _ at h
  dsimp only at h
  omega

include sizes in
theorem got_size (width cap stateWidth : Nat) (hh : header ≤ width)
    (hp : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hm : Q.size (marksRep rep) marks ≤ marksWidth width cap) :
    Q.size (gotRep rep R) (s, h, marks) ≤ stateWidth + marksWidth width cap + 3 * width := by
  have h1 := sizes.prod_le R.state (prod (rep.ty point₁) (marksRep rep)) (s, h, marks)
  have h2 := sizes.prod_le (rep.ty point₁) (marksRep rep) (h, marks)
  have h3 := hp h
  change Q.size (gotRep rep R) (s, h, marks) ≤ _ at h1
  dsimp only at h1 h2
  omega

include sizes in
theorem done_size (width cap routeWidth : Nat) (hh : header ≤ width)
    (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ routeWidth)
    (marks : List (Mark F)) (hm : Q.size (marksRep rep) marks ≤ marksWidth width cap) :
    Q.size (doneRep rep (bdI := bdI)) (result, marks) ≤ routeWidth + marksWidth width cap + width := by
  have h := sizes.prod_le bdI.out (marksRep rep) (result, marks)
  change Q.size (doneRep rep (bdI := bdI)) (result, marks) ≤ _ at h
  dsimp only at h
  omega

/-- Encoded width of a wrapper state over an attacker state of width `stateWidth`. -/
def stateWidth (width cap stateWidth routeWidth : Nat) : Nat :=
  max stateWidth routeWidth + marksWidth width cap + 5 * width

include sizes in
theorem state_size (width cap innerWidth routeWidth : Nat) (hh : header ≤ width)
    (hp : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (st : State R.machine (F := F))
    (hinner : ∀ s marks, st = ready R.machine s marks → Q.size R.state s ≤ innerWidth)
    (hgot : ∀ s h marks, st = gotHash R.machine s h marks → Q.size R.state s ≤ innerWidth)
    (hdone : ∀ result marks, st = done R.machine result marks → Q.size bdI.out result ≤ routeWidth)
    (hmarks : ∀ marks, (∃ s, st = ready R.machine s marks) ∨ (∃ s h, st = gotHash R.machine s h marks) ∨
      (∃ result, st = done R.machine result marks) → Q.size (marksRep rep) marks ≤ marksWidth width cap) :
    Q.size (stateRep rep R) st ≤ stateWidth width cap innerWidth routeWidth := by
  have hl := le_max_left innerWidth routeWidth
  have hr := le_max_right innerWidth routeWidth
  dsimp only [stateRep]
  rcases st with ⟨s, marks⟩ | ⟨s, h, marks⟩ | ⟨result, marks⟩
  · have hm := hmarks marks (Or.inl ⟨s, rfl⟩)
    have h1 := ready_size rep sizes R width cap innerWidth hh s (hinner s marks rfl) marks hm
    have h2 := sizes.sum_le (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, marks))
    dsimp only [Sum.elim, stateWidth] at *
    omega
  · have hm := hmarks marks (Or.inr (Or.inl ⟨s, h, rfl⟩))
    have h1 := got_size rep sizes R width cap innerWidth hh hp s (hgot s h marks rfl) h marks hm
    have h2 := sizes.sum_le (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (.inl (s, h, marks)))
    have h3 := sizes.sum_le (gotRep rep R) (doneRep rep (bdI := bdI)) (.inl (s, h, marks))
    dsimp only [Sum.elim, stateWidth] at *
    omega
  · have hm := hmarks marks (Or.inr (Or.inr ⟨result, rfl⟩))
    have h1 := done_size rep sizes width cap routeWidth hh result (hdone result marks rfl) marks hm
    have h2 := sizes.sum_le (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (.inr (result, marks)))
    have h3 := sizes.sum_le (gotRep rep R) (doneRep rep (bdI := bdI)) (.inr (result, marks))
    dsimp only [Sum.elim, stateWidth] at *
    omega

/-- Every tagged reply on a request of bounded size has bounded encoding. -/
theorem idx_size (width adapterTime : Nat)
    (caps : WeightedAGM.NativeHandler.PortCaps rep key Weights.syncMessage bdI ports width adapterTime)
    (hp : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (pos : GeneralRequest (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) randomBound)
    (hpos : WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width pos)
    (dir : (generalSpec (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁
      randomBound).Range pos) :
    Q.size bdI.idx ⟨pos, dir⟩ ≤ 8 * width := by
  rcases pos with (n | t) | m
  · exact (caps.randomTag ⟨n, dir⟩).1
  · exact (caps.hashTag t dir hpos (hp dir)).1
  · exact (caps.signTag m dir hpos (hp dir)).1

include sizes in
/-- The wrapper's own requests are sized when the attacker's are. -/
theorem translatePos_sized (width : Nat)
    (pos : GeneralRequest (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) randomBound)
    (hpos : WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width pos) :
    WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width (translatePos pos) := by
  rcases pos with (n | t) | m
  · exact hpos
  · exact hpos
  · exact (sizes.fst_le (rep.ty key) (rep.ty scalar) m).trans hpos

end Signatures.Runtime.SyncWrapGeneral
