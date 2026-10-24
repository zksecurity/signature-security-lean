import Proofs.Runtime.BackendCoronFinishParts

/-! Encoded frames retained during final extraction. The private store may grow
after the last hash, while the message cap stays fixed. -/

open PFunctor

namespace Signatures.Runtime.Coron.FinishCompiler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

def StartPre (width : Nat) (env : Env (cryptoBase F G₁ G₂ M M) StartEnv) : Prop :=
  Q.size (rep.ty message) env.1.1 ≤ width

def HashPre (width : Nat) (env : Env (cryptoBase F G₁ G₂ M M) HashEnv) : Prop :=
  Q.size (rep.ty point₁) env.1 ≤ width ∧ StartPre (Q := Q) rep width env.2

def ReadPre (qS width storeWidth cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS)) : Prop :=
  ReplyCompiler.StateInvariant (Q := Q) rep qS width storeWidth cap env.1 ∧ HashPre (Q := Q) rep width env.2

def LookupPre (qS width storeWidth cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (LookupEnv qS)) : Prop :=
  True ∧ ReadPre (Q := Q) rep qS width storeWidth cap env.2

def finishFrameWidth (width cap : Nat) : Nat := 32 * ReplyCompiler.writtenStoreWidth width cap

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)

include sizes

theorem forgery_size (out : M × G₁) (width : Nat) (hh : header ≤ width)
    (hm : Q.size (rep.ty message) out.1 ≤ width)
    (hg : Q.size (rep.ty point₁) out.2 ≤ width) :
    Q.size (rep.ty Forgery) out ≤ 3 * width := by
  have h := sizes.prod_le (rep.ty message) (rep.ty point₁) out
  dsimp only [Forgery, LanguageRepresentation.ty] at *
  omega

theorem startPre_size (qS width : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (env : Env (cryptoBase F G₁ G₂ M M) StartEnv) (hi : StartPre (Q := Q) rep width env) :
    Q.size (rep.env StartEnv) env ≤ 5 * width := by
  have hf := forgery_size rep sizes env.1 width hh hi (values.point env.1.2)
  have hp := sizes.prod_le (rep.ty Forgery) rep.data.unit env
  have hu := values.unit
  dsimp only [StartEnv, LanguageRepresentation.env] at *
  have he : env.2 = () := rfl
  grind only

theorem hashPre_size (qS width : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (env : Env (cryptoBase F G₁ G₂ M M) HashEnv) (hi : HashPre (Q := Q) rep width env) :
    Q.size (rep.env HashEnv) env ≤ 7 * width := by
  have ht := startPre_size rep sizes qS width hh values env.2 hi.2
  have hp := sizes.prod_le (rep.ty point₁) (rep.env StartEnv) env
  have hg := hi.1
  dsimp only [HashEnv, LanguageRepresentation.env] at *
  omega

theorem readPre_size (qS width storeWidth cap : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS))
    (hi : ReadPre (Q := Q) rep qS width storeWidth cap env) :
    Q.size (rep.env (ReadEnv qS)) env ≤ storeWidth + 8 * width := by
  have ht := hashPre_size rep sizes qS width hh values env.2 hi.2
  have hp := sizes.prod_le (rep.ty (machineStore qS)) (rep.env HashEnv) env
  have hs := hi.1.1
  dsimp only [ReadEnv, LanguageRepresentation.env] at *
  omega

theorem lookupResult_size (value : Bool × F) (qS width : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width) :
    Q.size (rep.ty LookupResult) value ≤ 3 * width := by
  have hp := sizes.prod_le rep.data.bool (rep.ty scalar) value
  have hb := values.bool value.1
  have hf := values.scalar value.2
  dsimp only [LookupResult, LanguageRepresentation.ty] at *
  omega

theorem lookupPre_size (qS width storeWidth cap : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (env : Env (cryptoBase F G₁ G₂ M M) (LookupEnv qS))
    (hi : LookupPre (Q := Q) rep qS width storeWidth cap env) :
    Q.size (rep.env (LookupEnv qS)) env ≤ storeWidth + 12 * width := by
  have ht := readPre_size rep sizes qS width storeWidth cap hh values env.2 hi.2
  have hp := sizes.prod_le (rep.ty LookupResult) (rep.env (ReadEnv qS)) env
  have hl := lookupResult_size rep sizes env.1 qS width hh values
  dsimp only [LookupEnv, LanguageRepresentation.env] at *
  omega

end Signatures.Runtime.Coron.FinishCompiler
