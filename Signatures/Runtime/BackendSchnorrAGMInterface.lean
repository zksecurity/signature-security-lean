import Signatures.Runtime.BackendLanguage
import Signatures.Runtime.SchnorrAGMReply

/-! Native boundaries for general Schnorr AGM callers. Encoders retain every
incoming group and coefficient row. Dependent reply tagging has actual backend
realizers; these proof-level functions do not supply free executable adapters. -/

open OracleComp OracleSpec PFunctor AlgebraicGroupModel.Interaction Schnorr.AGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Interface

open BackendProgram

abbrev SourceRequest (F G M : Type) := Explained F (Request M) (Group G)
abbrev sourceSpec (F G M : Type) := explainedSpec F (Group G) (Request M) (Reply F M)
abbrev SourceIndex (F G M : Type) := Σ i : SourceRequest F G M, (sourceSpec F G M).Range i
abbrev SourceForgery (F G M : Type) := Explained F (M × F) (Group G)
abbrev Args (A F G : Type) := A × List G × List (List F)
abbrev NativeRequest (F G M : Type) := Args Nat F G ⊕ (Args M F G ⊕ Args M F G)

abbrev argsTy (value : Ty CryptoAtom) : Ty CryptoAtom := .pair value (.pair (.list point₁) (.list (.list scalar)))
abbrev randomArgsTy : Ty CryptoAtom := argsTy .nat
abbrev groupArgsTy : Ty CryptoAtom := argsTy message
abbrev forgeryTy : Ty CryptoAtom := argsTy (.pair message scalar)
abbrev configTy : Ty CryptoAtom := .pair point₁ point₁
abbrev storeTy : Ty CryptoAtom := .pair configTy stateTy

def request {F G M : Type} (data : Request M) (groups : List G) (rows : List (List F)) : SourceRequest F G M :=
  ⟨⟨data, fun _ => groups⟩, fun _ => rows⟩

def encodeRequest {F G M : Type} (q : SourceRequest F G M) : NativeRequest F G M :=
  match q.value.data with
  | .random n => .inl (n, q.value.groups (), q.coefficients ())
  | .hash m => .inr (.inl (m, q.value.groups (), q.coefficients ()))
  | .sign m => .inr (.inr (m, q.value.groups (), q.coefficients ()))

def decodeRequest {F G M : Type} : NativeRequest F G M → SourceRequest F G M
  | .inl (n, groups, rows) => request (.random n) groups rows
  | .inr (.inl (m, groups, rows)) => request (.hash m) groups rows
  | .inr (.inr (m, groups, rows)) => request (.sign m) groups rows

/-- A proof relation for the final output boundary; executable conversion is
provided and charged separately by the solver's output adapter. -/
def encodeForgery {F G M : Type} (out : SourceForgery F G M) : Args (M × F) F G :=
  (out.value.data, out.value.groups (), out.coefficients ())

def decodeForgery {F G M : Type} (out : Args (M × F) F G) : SourceForgery F G M :=
  ⟨⟨out.1, fun _ => out.2.1⟩, fun _ => out.2.2⟩

@[simp] theorem decode_encodeForgery {F G M : Type} (out : SourceForgery F G M) :
    decodeForgery (encodeForgery out) = out := by cases out; rfl

@[simp] theorem encode_decodeForgery {F G M : Type} (out : Args (M × F) F G) :
    encodeForgery (decodeForgery out) = out := rfl

@[simp] theorem decode_encodeRequest {F G M : Type} (q : SourceRequest F G M) :
    decodeRequest (encodeRequest q) = q := by
  rcases q with ⟨⟨data, groups⟩, rows⟩
  cases data <;> rfl

@[simp] theorem encode_decodeRequest {F G M : Type} (q : NativeRequest F G M) :
    encodeRequest (decodeRequest q) = q := by
  rcases q with q | q | q <;> rfl

def randomTag {F G M : Type} (p : Args Nat F G × (Nat × List G)) : SourceIndex F G M :=
  ⟨request (.random p.1.1) p.1.2.1 p.1.2.2,
    ⟨Fin.ofNat (p.1.1 + 1) p.2.1, fun _ => p.2.2⟩⟩

def scalarTag {F G M : Type} (signing : Bool) (p : Args M F G × (F × List G)) : SourceIndex F G M :=
  if signing then ⟨request (.sign p.1.1) p.1.2.1 p.1.2.2, decodeGroupReply p.2⟩
  else ⟨request (.hash p.1.1) p.1.2.1 p.1.2.2, decodeGroupReply p.2⟩

theorem randomTag_fin {F G M : Type} (n : Nat) (groups : List G) (rows : List (List F))
    (r : Fin (n + 1)) (replyGroups : List G) :
    randomTag (M := M) ((n, groups, rows), (r.val, replyGroups)) =
      ⟨request (.random n) groups rows, ⟨r, fun _ => replyGroups⟩⟩ := by
  have h : Fin.ofNat (n + 1) r.val = r := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt r.isLt
  simp only [randomTag, h]

def defaultReply {F G M : Type} [Zero F] (q : SourceRequest F G M) : (sourceSpec F G M).Range q := by
  rcases q with ⟨⟨request, groups⟩, rows⟩
  cases request with
  | random n => exact ⟨(0 : Fin (n + 1)), fun _ => []⟩
  | hash m => exact scalarReply (0 : F)
  | sign m => exact scalarReply (0 : F)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def positions : C.Str (NativeRequest F G₁ M) :=
  StepClass.HasSum.sum (rep.ty randomArgsTy) (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy))

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)

structure Ports where
  request : Q.Realizer bd.pos (positions rep) encodeRequest
  randomTag : Q.Realizer (StepClass.HasProd.prod (rep.ty randomArgsTy) (rep.ty (groupReplyTy .nat))) bd.idx randomTag
  scalarTag : (signing : Bool) →
    Q.Realizer (StepClass.HasProd.prod (rep.ty groupArgsTy) (rep.ty scalarGroupReplyTy)) bd.idx (scalarTag signing)

end Signatures.Runtime.SchnorrAGM.Native.Interface
