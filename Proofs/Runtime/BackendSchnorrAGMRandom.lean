import Proofs.Runtime.BackendSchnorrAGMSigningDispatchBudget
import Proofs.Runtime.BackendUniformSampling

/-! Native Schnorr randomness handling. Every request executes one dynamic
uniform query, including malformed requests. The compiled scan marks malformed
state, and the reply constructor supplies an empty group list. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native.Random

open BackendProgram

abbrev inputTy : Ty CryptoAtom := .pair (.list point₁) (.pair (.list (.list scalar)) (.pair .nat stateTy))
abbrev preparedTy : Ty CryptoAtom := .pair .nat stateTy
abbrev outputTy : Ty CryptoAtom := .pair (groupReplyTy .nat) stateTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

def marked {F G M : Type} (empty : Bool) (s : EncodedState F G M) : EncodedState F G M :=
  (s.1, s.2.1, s.2.2.1, if empty then s.2.2.2.1 else true, s.2.2.2.2)

def prepareValue {F G M : Type} (input : List G × List (List F) × Nat × EncodedState F G M) :=
  (input.2.2.1, marked input.1.isEmpty input.2.2.2)

def prepareWith (scan : Expr CryptoOp [.list point₁, inputTy] .bool) : Expr CryptoOp [inputTy] preparedTy :=
  .letE (.fst v0) (.letE scan
    (let state := Expr.snd (Expr.snd (Expr.snd v2))
     let metadata := Expr.snd state
     .pair (.fst (.snd (.snd v2)))
       (.pair (.fst state) (.pair (.fst metadata) (.pair (.fst (.snd metadata))
         (.pair (.branch v0 (.fst (.snd (.snd metadata))) (.bool true))
           (.snd (.snd (.snd metadata)))))))))

def prepareExpression : Expr CryptoOp [inputTy] preparedTy := prepareWith ListEmpty.scan

def wrapValue {F G M : Type} (input : Nat × EncodedState F G M) : (Nat × List G) × EncodedState F G M :=
  ((input.1, []), input.2)

def wrapExpression : Expr CryptoOp [preparedTy] outputTy :=
  .pair (.pair (.fst v0) .nil) (.snd v0)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem prepareExpression_value (cost : PrimitiveCosts) (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    prepareExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = prepareValue input := by
  dsimp only [prepareExpression, prepareWith, Expr.denote, Var.get]
  rw [ListEmpty.denote]
  rfl

theorem wrapExpression_value (cost : PrimitiveCosts) (input : preparedTy.Value (cryptoBase F G₁ G₂ K M)) :
    wrapExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = wrapValue input := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def prepare : Q.Realizer (rep.ty inputTy) (rep.ty preparedTy) prepareValue :=
  (Q.compose (Read.frame rep data inputTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepareExpression)).castFunction
      (by funext input; exact prepareExpression_value cost input)

def wrap : Q.Realizer (rep.ty preparedTy) (rep.ty outputTy) wrapValue :=
  (Q.compose (Read.frame rep data preparedTy)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive wrapExpression)).castFunction
      (by funext input; exact wrapExpression_value cost input)

variable {iface : Interface (C := C) unifSpec} (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))

def code : Code Q unifSpec iface (rep.ty inputTy) (rep.ty outputTy) :=
  .seq (.atomic (prepare rep data cost primitive))
    (.seq (.first (rep.ty stateTy) (UniformSampling.code rep.data ports)) (.atomic (wrap rep data cost primitive)))

theorem denote (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive ports).denote input =
      (fun r : Fin (input.2.2.1 + 1) => ((r.val, []), marked input.1.isEmpty input.2.2.2)) <$>
        (unifSpec.query input.2.2.1 : ProbComp (Fin (input.2.2.1 + 1))) := by
  simp only [code, Code.denote, pure_bind, bind_pure_comp, UniformSampling.denote, Functor.map_map]
  rfl

theorem source [SampleableType F] (g pk : G₁) (s : State F G₁ M) (n : Nat)
    (groups : List G₁) (rows : List (List F)) :
    (code rep data cost primitive ports).denote (groups, rows, n, encodeState s) =
      (fun p => ((p.1.data.val, p.1.groups ()), encodeState p.2)) <$>
        (handler g pk ⟨⟨.random n, fun _ => groups⟩, fun _ => rows⟩).run s := by
  rw [denote]
  cases groups <;>
    simp only [handler, StateT.run, List.cons_ne_nil, ite_true, ite_false,
      bind_pure_comp, Functor.map_map, List.isEmpty_nil, List.isEmpty_cons]
  · rfl
  · rfl

theorem description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (code rep data cost primitive ports).descriptionSize sizes ≤
      sizes.localSize ports.request + sizes.localSize ports.response + 2048 * allowance + 16 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (Read.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hp : sizes.localSize (prepare rep data cost primitive) ≤ 1024 * allowance := by
    rw [prepare, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
        (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) prepareExpression)
    refine h.trans ?_
    simp only [prepareExpression, prepareWith, ListEmpty.scan, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hw : sizes.localSize (wrap rep data cost primitive) ≤ 128 * allowance := by
    rw [wrap, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe preparedTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
        (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl) wrapExpression)
    refine h.trans ?_
    simp only [wrapExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hs := UniformSampling.description rep.data ports sizes
  dsimp only [code, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native.Random
