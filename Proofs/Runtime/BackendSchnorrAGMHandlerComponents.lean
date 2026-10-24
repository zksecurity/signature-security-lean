import Proofs.Runtime.BackendSchnorrAGMInterface
import Proofs.Runtime.BackendSchnorrAGMRandomBudget
import Proofs.Runtime.BackendSchnorrAGMHashDispatchBudget

/-! Common-store adapters for the three implemented Schnorr handlers. The
generator and public key are represented state, retained across every call.
Hash replies receive an actual compiled empty-group-list constructor. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

open BackendProgram Interface

abbrev argsStoreTy (args : Ty CryptoAtom) : Ty CryptoAtom := .pair args storeTy
abbrev savedTy (input : Ty CryptoAtom) : Ty CryptoAtom := .pair input configTy
abbrev resultTy (reply : Ty CryptoAtom) : Ty CryptoAtom := .pair reply storeTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here

def randomInputExpression : Expr CryptoOp [argsStoreTy randomArgsTy] (savedTy Random.inputTy) :=
  let args := Expr.fst v0
  let store := Expr.snd v0
  .pair (.pair (.fst (.snd args)) (.pair (.snd (.snd args)) (.pair (.fst args) (.snd store)))) (.fst store)

def hashInputExpression : Expr CryptoOp [argsStoreTy groupArgsTy] (savedTy HashDispatch.inputTy) :=
  let args := Expr.fst v0
  let store := Expr.snd v0
  .pair (.pair (.fst args) (.pair (.fst (.snd args)) (.pair (.snd (.snd args)) (.snd store)))) (.fst store)

def signingInputExpression : Expr CryptoOp [argsStoreTy groupArgsTy] (savedTy SigningDispatch.inputTy) :=
  let args := Expr.fst v0
  let store := Expr.snd v0
  .pair (.pair (.fst (.snd args)) (.pair (.snd (.snd args))
    (.pair (.fst (.fst store)) (.pair (.snd (.fst store)) (.pair (.fst args) (.snd store)))))) (.fst store)

def groupOutputExpression (value : Ty CryptoAtom) :
    Expr CryptoOp [savedTy (.pair (groupReplyTy value) stateTy)] (resultTy (groupReplyTy value)) :=
  .pair (.fst (.fst v0)) (.pair (.snd v0) (.snd (.fst v0)))

def hashOutputExpression : Expr CryptoOp [savedTy Read.outputTy] (resultTy scalarGroupReplyTy) :=
  .pair (.pair (.fst (.fst v0)) .nil) (.pair (.snd v0) (.snd (.fst v0)))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def localCode {a b : Ty CryptoAtom} (e : Expr CryptoOp [a] b) :
    Q.Realizer (rep.ty a) (rep.ty b) (fun input => e.denote (arithmetic F G₁ G₂ K M cost) (input, ())) :=
  Q.compose (Read.frame rep data a) (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e)

def random (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface)) :
    Code Q unifSpec iface (rep.ty (argsStoreTy randomArgsTy)) (rep.ty (resultTy (groupReplyTy .nat))) :=
  .seq (.atomic (localCode rep data cost primitive randomInputExpression))
    (.seq (.first (rep.ty configTy) (Random.code rep data cost primitive ports))
      (.atomic (localCode rep data cost primitive (groupOutputExpression .nat))))

def hash (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)) :
    Code Q unifSpec iface (rep.ty (argsStoreTy groupArgsTy)) (rep.ty (resultTy scalarGroupReplyTy)) :=
  .seq (.atomic (localCode rep data cost primitive hashInputExpression))
    (.seq (.first (rep.ty configTy) (HashDispatch.code rep data cost primitive sampler))
      (.atomic (localCode rep data cost primitive hashOutputExpression)))

def signing (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)) :
    Code Q unifSpec iface (rep.ty (argsStoreTy groupArgsTy)) (rep.ty (resultTy scalarGroupReplyTy)) :=
  .seq (.atomic (localCode rep data cost primitive signingInputExpression))
    (.seq (.first (rep.ty configTy) (SigningDispatch.code rep data cost primitive sampler))
      (.atomic (localCode rep data cost primitive (groupOutputExpression scalar))))

theorem random_denote (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (args : Interface.Args Nat F G₁) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (random rep data cost primitive ports).denote (args, saved) =
      (fun p => (p.1, saved.1, p.2)) <$>
        (Random.code rep data cost primitive ports).denote (args.2.1, args.2.2, args.1, saved.2) := by
  simp only [random, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem hash_denote (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (args : Interface.Args M F G₁) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (hash rep data cost primitive sampler).denote (args, saved) =
      (fun p => ((p.1, []), saved.1, p.2)) <$>
        (HashDispatch.code rep data cost primitive sampler).denote (args.1, args.2.1, args.2.2, saved.2) := by
  simp only [hash, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem signing_denote (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (args : Interface.Args M F G₁) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (signing rep data cost primitive sampler).denote (args, saved) =
      (fun p => (p.1, saved.1, p.2)) <$>
        (SigningDispatch.code rep data cost primitive sampler).denote
          (args.2.1, args.2.2, saved.1.1, saved.1.2, args.1, saved.2) := by
  simp only [signing, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem localCode_description {a b : Ty CryptoAtom} (e : Expr CryptoOp [a] b)
    (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (localCode rep data cost primitive e) ≤
      Expression.descriptionBound allowance primitiveSize e + 4 * allowance := by
  have hframe : sizes.localSize (Read.frame rep data a) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have h := laws.compose_bound hframe
    (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws primitiveSize hp e)
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.HandlerComponents
