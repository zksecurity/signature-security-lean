import Signatures.Runtime.BackendSchnorrROMCallerOutput
import Signatures.Runtime.BackendSchnorrROMHandlerDescription
import Signatures.Runtime.BackendSchnorrRawFork

/-! The actual ordinary-ROM pass: initialize separate caches, run an arbitrary
caller, convert its forgery, and perform the final live-cache hash. An empty
result list represents cutoff; a singleton contains the completed pass. This
requires no default message and fits the existing native fork's value language. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeInterface NativeComponents

abbrev inputTy : Ty CryptoAtom := NativeFork.passInput configTy
abbrev outputTy : Ty CryptoAtom := .list cachePassOutput
abbrev resultTy : Ty CryptoAtom := NativeFork.passOutput outputTy

def optionView {A : Type} : Option A → Unit ⊕ A
  | none => .inl ()
  | some out => .inr out

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here

def initialExpression : Expr CryptoOp [inputTy] (withStore point₁) :=
  .pair (.snd (.snd v0)) (.pair (.pair (.snd v0) (.pair .nil .nil)) (.fst v0))

def verifyInput : Expr CryptoOp [withStore forgery] (.pair (withStore hashKey) forgery) :=
  .pair (.pair (.pair (.fst (.fst v0)) (.fst (.snd (.fst v0)))) (.snd v0)) (.fst v0)

def verifyOutput : Expr CryptoOp [.pair (withStore scalar) forgery] (NativeFork.passOutput cachePassOutput) :=
  .pair (.pair (.pair (.snd v0) (.fst (.fst v0))) (.fst (.snd (.fst v0)))) (.snd (.snd (.fst v0)))

def singletonExpression : Expr CryptoOp [NativeFork.passOutput cachePassOutput] resultTy :=
  .pair (.cons (.fst v0) .nil) (.snd v0)

def cutoffExpression : Expr CryptoOp [withStore .unit] resultTy :=
  .pair .nil (.snd (.snd v0))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))

/-- Actual local representation conversions, separately charged by their
runtime and description contracts. -/
structure DataPorts where
  input : Q.Realizer (rep.ty point₁) bd.input id
  output : Q.Realizer bd.out (rep.ty forgery) id
  optional : Q.Realizer (StepClass.HasOption.option bd.out)
    (StepClass.HasSum.sum rep.data.unit bd.out) optionView

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def setup : Code Q unifSpec iface (rep.ty inputTy) (StepClass.HasProd.prod bd.input (rep.ty storeTy)) :=
  .seq (.atomic (localCode rep data cost primitive initialExpression))
    (.first (rep.ty storeTy) (.atomic boundary.input))

def verify : Code Q unifSpec iface (rep.ty (withStore forgery)) (rep.ty (NativeFork.passOutput cachePassOutput)) :=
  wrap rep data cost primitive forgery verifyInput verifyOutput (NativeComponents.finalHash rep data cost primitive sampler)

def finishSome : Code Q unifSpec iface (StepClass.HasProd.prod bd.out (rep.ty storeTy)) (rep.ty resultTy) :=
  .seq (.first (rep.ty storeTy) (.atomic boundary.output))
    (.seq (verify rep data cost primitive sampler) (.atomic (localCode rep data cost primitive singletonExpression)))

def cutoff : Code Q unifSpec iface (rep.ty (withStore .unit)) (rep.ty resultTy) :=
  .atomic (localCode rep data cost primitive cutoffExpression)

variable [QD : Q.IsDistributive]

def terminal : Code Q unifSpec iface (Caller.result (bd := bd) (rep.ty storeTy)) (rep.ty resultTy) :=
  .seq (.first (rep.ty storeTy) (.atomic boundary.optional))
    (.seq (.atomic (QD.distribute rep.data.unit bd.out (rep.ty storeTy)))
      (.branch (cutoff rep data cost primitive) (finishSome rep bd boundary data cost primitive sampler)))

variable [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F]
  (ports : Ports (Q := Q) rep bd)
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def code (fuel : Nat) : Code Q unifSpec iface (rep.ty inputTy) (rep.ty resultTy) :=
  .seq (setup rep bd boundary data cost primitive)
    (.seq (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts sampler R fuel)
      (terminal rep bd boundary data cost primitive sampler))

omit QD [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F] in
theorem setup_denote (tape : Shared.Tape F) (g pk : G₁) :
    (setup (iface := iface) rep bd boundary data cost primitive).denote (tape, g, pk) =
      pure (pk, ((g, pk), [], []), tape) := by
  simp only [setup, Code.denote, pure_bind, map_pure]
  rfl

omit QD [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F] [C.HasOption] in
theorem verify_denote (out : M × G₁ × F) (saved : Shared.Store F G₁ M) :
    (verify rep data cost primitive sampler).denote (out, saved) =
      (fun p => (((out, p.1), p.2.1), p.2.2)) <$>
        (NativeComponents.finalHash rep data cost primitive sampler).denote ((out.1, out.2.1), saved) := by
  simp only [verify, NativeComponents.wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

omit QD [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F] in
theorem finishSome_denote (out : M × G₁ × F) (saved : Shared.Store F G₁ M) :
    (finishSome rep bd boundary data cost primitive sampler).denote (out, saved) =
      (fun p => ([((out, p.1), p.2.1)], p.2.2)) <$>
        (NativeComponents.finalHash rep data cost primitive sampler).denote ((out.1, out.2.1), saved) := by
  simp only [finishSome, Code.denote, map_pure, pure_bind]
  rw [verify_denote]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

omit QD [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F] [C.HasOption] in
theorem cutoff_denote (saved : Shared.Store F G₁ M) :
    (cutoff (iface := iface) rep data cost primitive).denote ((), saved) = pure ([], saved.2) := rfl

omit [Q.HasOption] [OptionCode (Q := Q)] [SampleableType F] in
theorem terminal_denote (result : Option (M × G₁ × F)) (saved : Shared.Store F G₁ M) :
    (terminal rep bd boundary data cost primitive sampler).denote (result, saved) =
      match result with
      | none => pure ([], saved.2)
      | some out => (fun p => ([((out, p.1), p.2.1)], p.2.2)) <$>
          (NativeComponents.finalHash rep data cost primitive sampler).denote ((out.1, out.2.1), saved) := by
  cases result with
  | none =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inl, map_pure, pure_bind]
      rfl
  | some out =>
      simp only [terminal, Code.denote, optionView, Sum.elim_inr, map_pure, pure_bind]
      exact finishSome_denote rep bd boundary data cost primitive sampler out saved

omit [SampleableType F] in
theorem code_denote (fuel : Nat) (tape : Shared.Tape F) (g pk : G₁) :
    (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel).denote (tape, g, pk) =
      (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).denote
        (pk, ((g, pk), [], []), tape) >>= fun p =>
          (terminal rep bd boundary data cost primitive sampler).denote p := by
  simp only [code, Code.denote]
  rw [setup_denote, pure_bind]

end Signatures.Runtime.Schnorr.ListROM.NativePass
