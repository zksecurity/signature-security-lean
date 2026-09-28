import Signatures.Runtime.AGMOracle
import Signatures.Runtime.Refinement

/-! Exact adaptive correspondence to the native AGM oracle, including decoded query keys
and messages, repeated replies, and chronological transcripts. Representation maps are
proof-only; no decoder or transcript reversal is a free executable machine operation. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

def transcriptView {I J N L G : Type} (index : I → J) (message : N → L)
    (tr : List (I × G) × List (N × G)) : Model.LazyAGM.Transcript J L G :=
  (tr.1.reverse.map fun p => (index p.1, p.2), tr.2.reverse.map fun p => (message p.1, p.2))

def chronological {I J N L G C : Type} (index : I → J) (message : N → L)
    (state : C × List (I × G) × List (N × G)) : C × Model.LazyAGM.Transcript J L G :=
  (state.1, transcriptView index message state.2)

variable {F G₁ G₂ K M I N : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {indexTy messageTy configTy : Ty CryptoAtom}

noncomputable def sourceSemantics
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) → I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N) (randomBound : Nat) :
    Semantics (cryptoBase F G₁ G₂ K M) (Command indexTy messageTy randomBound)
      (Model.LazyAGM.advSpec I N G₁) := fun cmd arg => match cmd with
  | .random n => liftM ((Model.LazyAGM.advSpec I N G₁).query (.inl (.inl n.val)))
  | .hash => liftM ((Model.LazyAGM.advSpec I N G₁).query (.inl (.inr (index arg))))
  | .sign => liftM ((Model.LazyAGM.advSpec I N G₁).query (.inr (message arg)))

noncomputable def referenceHandler
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) → I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N)
    (H : configTy.Value (cryptoBase F G₁ G₂ K M) → I → G₁)
    (sign : configTy.Value (cryptoBase F G₁ G₂ K M) → N → G₁) (randomBound : Nat) :
    SemanticsM (cryptoBase F G₁ G₂ K M) (Command indexTy messageTy randomBound)
      (StateT (configTy.Value (cryptoBase F G₁ G₂ K M) × Model.LazyAGM.Transcript I N G₁) ProbComp) :=
  fun cmd arg state => (fun p => (p.1, state.1, p.2)) <$>
    (simulateQ (Model.LazyAGM.fixedImpl (H state.1) (sign state.1))
      (sourceSemantics index message randomBound cmd arg)).run state.2

theorem handler_refines (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁)
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) → I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N)
    (H : configTy.Value (cryptoBase F G₁ G₂ K M) → I → G₁)
    (S : configTy.Value (cryptoBase F G₁ G₂ K M) → N → G₁)
    (hHash : ∀ cfg i, hash.denote (arithmetic F G₁ G₂ K M cost) (i, cfg, ()) = H cfg (index i))
    (hSign : ∀ cfg m, sign.denote (arithmetic F G₁ G₂ K M cost) (m, cfg, ()) = S cfg (message m))
    (randomBound : Nat) {a b} (cmd : Command indexTy messageTy randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateRefines (chronological index message)
      (Run.value <$> machineHandler cost sampling hash sign randomBound cmd arg)
      (referenceHandler index message H S randomBound cmd arg) := by
  intro state
  have hm := StateT.run_map (m := ProbComp) Run.value
    (machineHandler (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost sampling hash sign randomBound cmd arg) state
  simp only [StateT.run] at hm ⊢
  have hr := machineHandler_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
    cost sampling hash sign randomBound cmd arg state
  simp only [StateT.run] at hr
  rw [hm, hr]
  rcases state with ⟨cfg, hashes, signed⟩
  cases cmd with
  | random n =>
      dsimp [machineRoutines, Program.run, Expr.run, Machine.effects, StateT.run, StateT.bind, StateT.pure]
      simp only [referenceHandler, sourceSemantics, simulateQ_query, Model.LazyAGM.fixedImpl,
        Model.LazyAGM.handler, chronological, transcriptView, StateT.run, StateT.mk, bind_pure_comp]
      have hu := StateT.run_map (m := ProbComp)
        (fun r : Run (Fin (n.val + 1)) => (⟨r.value, 1 + r.steps + 1⟩ : Run (Fin (n.val + 1))))
        (Machine.effects (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
          sampling (oracleStore indexTy messageTy configTy) (.uniform n.val) ()) (cfg, hashes, signed)
      simp only [StateT.run] at hu
      rw [hu]
      simp [Machine.effects, Functor.map_map]
  | hash =>
      have hx := machineHash_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        (messageTy := messageTy) cost sampling hash arg cfg (hashes, signed)
      simp only [StateT.run] at hx
      simp only [machineRoutines]
      rw [hx]
      simp [referenceHandler, sourceSemantics, Model.LazyAGM.fixedImpl, Model.LazyAGM.handler,
        StateT.run, StateT.mk, chronological, transcriptView, hHash]
  | sign =>
      have hx := machineSign_run (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
        (indexTy := indexTy) cost sampling sign arg cfg (hashes, signed)
      simp only [StateT.run] at hx
      simp only [machineRoutines]
      rw [hx]
      simp [referenceHandler, sourceSemantics, Model.LazyAGM.fixedImpl, Model.LazyAGM.handler,
        StateT.run, StateT.mk, chronological, transcriptView, hSign]

omit [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [DecidableEq K] [DecidableEq M] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] in
theorem reference_embed
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) → I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N)
    (H : configTy.Value (cryptoBase F G₁ G₂ K M) → I → G₁)
    (S : configTy.Value (cryptoBase F G₁ G₂ K M) → N → G₁)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M)) (randomBound : Nat)
    {a b} (cmd : Command indexTy messageTy randomBound a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateRefines (fun tr => (cfg, tr))
      (simulateQ (Model.LazyAGM.fixedImpl (H cfg) (S cfg))
        (sourceSemantics index message randomBound cmd arg))
      (referenceHandler index message H S randomBound cmd arg) := by
  intro tr
  rfl

/-- Entire inlined adaptive source execution, not just individual request answers, agrees
with native simulation. The fixed configuration is retained internally and never exposed
through the source oracle interface. -/
theorem machineSimulation_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hash : Expr CryptoOp [indexTy, configTy] point₁)
    (sign : Expr CryptoOp [messageTy, configTy] point₁)
    (index : indexTy.Value (cryptoBase F G₁ G₂ K M) → I)
    (message : messageTy.Value (cryptoBase F G₁ G₂ K M) → N)
    (H : configTy.Value (cryptoBase F G₁ G₂ K M) → I → G₁)
    (S : configTy.Value (cryptoBase F G₁ G₂ K M) → N → G₁)
    (hHash : ∀ cfg i, hash.denote (arithmetic F G₁ G₂ K M cost) (i, cfg, ()) = H cfg (index i))
    (hSign : ∀ cfg m, sign.denote (arithmetic F G₁ G₂ K M cost) (m, cfg, ()) = S cfg (message m))
    (randomBound : Nat) {Γ a} (code : Program CryptoOp (Command indexTy messageTy randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cfg : configTy.Value (cryptoBase F G₁ G₂ K M))
    (tr : (transcriptTy indexTy messageTy).Value (cryptoBase F G₁ G₂ K M)) :
    (fun z => (z.1.value, transcriptView index message z.2.2)) <$>
      (((code.inline (machineRoutines hash sign randomBound)).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy configTy)) env).run (cfg, tr)) =
      (simulateQ (Model.LazyAGM.fixedImpl (H cfg) (S cfg))
        (code.denote (arithmetic F G₁ G₂ K M cost) (sourceSemantics index message randomBound) env)).run
        (transcriptView index message tr) := by
  rw [Program.inline_run, Program.denote_simulate]
  have hs : StateRefines (chronological index message)
      (Run.value <$> code.run (arithmetic F G₁ G₂ K M cost)
        (machineHandler cost sampling hash sign randomBound) env)
      (code.denote (arithmetic F G₁ G₂ K M cost) (referenceHandler index message H S randomBound) env) := by
    rw [Program.run_erase]
    exact code.denote_refines _ _ _ _
      (handler_refines cost sampling hash sign index message H S hHash hSign randomBound) env
  have hn := code.denote_refines (arithmetic F G₁ G₂ K M cost) (fun tr => (cfg, tr)) _ _
    (reference_embed index message H S cfg randomBound) env (transcriptView index message tr)
  have hh := hs (cfg, tr)
  have hm := StateT.run_map (m := ProbComp) Run.value
    (code.run (arithmetic F G₁ G₂ K M cost) (machineHandler cost sampling hash sign randomBound) env)
    (cfg, tr)
  simp only [StateT.run] at hm hh hn
  rw [hm] at hh
  change _ = code.denote (arithmetic F G₁ G₂ K M cost)
    (referenceHandler index message H S randomBound) env (cfg, transcriptView index message tr) at hh
  rw [← hn] at hh
  have he := congrArg (Functor.map (fun p => (p.1, p.2.2))) hh
  simpa only [Functor.map_map, chronological, Function.comp_def, Prod.eta, id_map',
    StateT.run, machineHandler] using he

end Signatures.Runtime.AGM
