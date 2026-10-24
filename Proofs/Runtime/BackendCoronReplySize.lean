import Proofs.Runtime.BackendCoronReplyParts

/-! Encoded-size invariants for every retained environment of the native Coron
reply. Private-cache inputs need bounds only on their stored keys and values.
The ambient store's size is explicit; its post-write bound may be larger. -/

open PFunctor

namespace Signatures.Runtime.Coron.ReplyCompiler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

def StoreReady (qS width cap : Nat) (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size (rep.ty (machineStore qS)) saved ≤ width ∧
    CacheCompiler.Entries (Q := Q) rep (key := message) (val := scalar) width saved.2.1 ∧
    saved.2.1.length ≤ cap ∧
    CacheCompiler.Entries (Q := Q) rep (key := message) (val := boundedNat qS) width saved.2.2.1 ∧
    saved.2.2.1.length ≤ cap

def ReadPre (qS width cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS)) : Prop :=
  StoreReady (Q := Q) rep qS width cap env.1 ∧ Q.size (rep.ty message) env.2.1 ≤ width

def ScalarPre (qS width cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ScalarEnv qS)) : Prop :=
  CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1) env.1 ∧
    ReadPre (Q := Q) rep qS width cap env.2

def BothPre (qS width cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (BothEnv qS)) : Prop :=
  CacheCompiler.Output (Q := Q) rep (key := message) (val := boundedNat qS) width (cap + 1) env.1 ∧
    ScalarPre (Q := Q) rep qS width cap env.2

def WrittenPre (qS width cap : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS)) : Prop :=
  True ∧ BothPre (Q := Q) rep qS width cap env.2

def replyFrameWidth (width cap : Nat) : Nat := 64 * (cap + 2) * width
def writtenStoreWidth (width cap : Nat) : Nat := (8 * cap + 24) * width

omit [C.HasSum] [C.HasOption] in
/-- The source simulation's encountered-message invariant supplies the native
handler's cache precondition. The encoded-store cap is supplied by
`machineState_encoded_size`, independently of any finite message universe. -/
theorem storeReady_machineState (qS width cap : Nat) (g X h : G₁) (state : CacheState F M qS)
    (hs : Q.size (rep.ty (machineStore qS)) (machineState g X h state) ≤ width)
    (hm : state.Messages (fun m => Q.size (rep.ty message) m ≤ width))
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width)
    (hn : state.size ≤ cap) : StoreReady (Q := Q) rep qS width cap (machineState g X h state) := by
  exact ⟨hs, (fun p hp => ⟨hm.1 p hp, hf p.2⟩), (Nat.le_max_left _ _).trans hn,
    (fun p hp => ⟨hm.2.1 p hp, hc p.2⟩), ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans hn⟩

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem readPre_size (qS width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS)) (hi : ReadPre (Q := Q) rep qS width cap env) :
    Q.size (rep.env (ReadEnv qS)) env ≤ 5 * width := by
  have hs := hi.1.1
  have hm := hi.2
  have hprod := @sizes.prod_le
  have he : env.2.2 = () := rfl
  dsimp only [ReadEnv, LanguageRepresentation.env] at *
  grind only

include lists

theorem scalarPre_size (qS width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (env : Env (cryptoBase F G₁ G₂ M M) (ScalarEnv qS)) (hi : ScalarPre (Q := Q) rep qS width cap env) :
    Q.size (rep.env (ScalarEnv qS)) env ≤ (4 * cap + 13) * width := by
  have hr := CacheCompiler.output_size rep sizes lists width (cap + 1) hh env.1 hi.1
  have ht := readPre_size rep sizes qS width cap hh hu env.2 hi.2
  have hp := sizes.prod_le (rep.ty ScalarResult) (rep.env (ReadEnv qS)) env
  dsimp only [ScalarEnv, LanguageRepresentation.env] at *
  nlinarith

theorem bothPre_size (qS width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (env : Env (cryptoBase F G₁ G₂ M M) (BothEnv qS)) (hi : BothPre (Q := Q) rep qS width cap env) :
    Q.size (rep.env (BothEnv qS)) env ≤ (8 * cap + 21) * width := by
  have hr := CacheCompiler.output_size rep sizes lists width (cap + 1) hh env.1 hi.1
  have ht := scalarPre_size rep sizes lists qS width cap hh hu env.2 hi.2
  have hp := sizes.prod_le (rep.ty (CoinResult qS)) (rep.env (ScalarEnv qS)) env
  dsimp only [BothEnv, LanguageRepresentation.env] at *
  nlinarith

theorem writtenPre_size (qS width cap : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS)) (hi : WrittenPre (Q := Q) rep qS width cap env) :
    Q.size (rep.env (WrittenEnv qS)) env ≤ (8 * cap + 23) * width := by
  have ht := bothPre_size rep sizes lists qS width cap hh hu env.2 hi.2
  have hp := sizes.prod_le rep.data.unit (rep.env (BothEnv qS)) env
  have he : env.1 = () := rfl
  dsimp only [WrittenEnv, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem writeState_size (qS width cap : Nat) (signing : Bool) (hh : header ≤ width)
    (env : Env (cryptoBase F G₁ G₂ M M) (BothEnv qS)) (hi : BothPre (Q := Q) rep qS width cap env) :
    Q.size (rep.ty (machineStore qS)) ((writeState qS signing).denote (arithmetic F G₁ G₂ M M cost) env) ≤
      writtenStoreWidth width cap := by
  have hc := CacheCompiler.output_size rep sizes lists width (cap + 1) hh env.1 hi.1
  have hf := CacheCompiler.output_size rep sizes lists width (cap + 1) hh env.2.1 hi.2.1
  have hs := hi.2.2.1.1
  have hm := hi.2.2.2
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  rw [writeState_denote]
  cases signing <;>
    dsimp only [writtenStoreWidth, machineStore, LanguageRepresentation.ty, Bool.false_eq_true, ite_true, ite_false] at * <;>
    grind only

end Signatures.Runtime.Coron.ReplyCompiler
