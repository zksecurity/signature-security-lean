import Signatures.Runtime.BackendCallerBudget
import Signatures.Runtime.BackendWithin
import Signatures.Runtime.BackendMachine
import Signatures.Runtime.BackendCoron
import Signatures.Runtime.BackendLanguageCost
import Signatures.Runtime.BackendCallerSize
import Signatures.Runtime.BackendCallerResource
import Signatures.Runtime.BackendCoronCost
import Signatures.Runtime.BackendCoronCacheCost
import Signatures.Runtime.BackendCoronReplyBudget
import Signatures.Runtime.BackendCoronFinishBudget
import Signatures.Runtime.BackendCoronDescription
import Signatures.Runtime.BackendCoronCaller
import Signatures.Runtime.BackendCoronHandlerDescription
import Signatures.Runtime.BackendCallerIndexedResource
import Signatures.Runtime.BackendCoronCallerBudget
import Signatures.Runtime.BackendCoronSolverWithin
import Signatures.Runtime.BackendCoronSecurity
import Signatures.Runtime.BackendCoronPolynomial
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram

namespace SignaturesTest.BackendAssembly

-- Early return executes one body step and charges loop administration. It does
-- not execute the stop program, even when a larger iteration cap remains.
example {I S B : Type} {spec : OracleSpec I}
    (body : S → OracleComp spec (Run (B ⊕ S)))
    (stop : S → OracleComp spec (Run B)) (fee : Nat → S → Nat)
    (state : S) (value : B) (steps fuel : Nat)
    (hbody : body state = pure ⟨.inl value, steps⟩) :
    loopRun fee body stop (fuel + 1) state = pure ⟨value, steps + fee (fuel + 1) state⟩ := by
  simp [loopRun, hbody]

-- Fuel exhaustion still runs and charges the explicit stop code.
example {I S B : Type} {spec : OracleSpec I}
    (body : S → OracleComp spec (Run (B ⊕ S)))
    (stop : S → OracleComp spec (Run B)) (fee : Nat → S → Nat)
    (state : S) (value : B) (steps : Nat)
    (hstop : stop state = pure ⟨value, steps⟩) :
    loopRun fee body stop 0 state = pure ⟨value, steps + fee 0 state⟩ := by
  simp [loopRun, chargeRun, hstop]

-- A dynamic loop uses the updated state on later iterations and charges the
-- changing body cost, every loop test, and the final zero test.
example {I : Type} {spec : OracleSpec I} :
    iterationRun (fun n state => n + state)
      (fun state => (pure ⟨state + 1, 2 * state⟩ : OracleComp spec (Run Nat))) 2 3 =
        pure ⟨5, 29⟩ := by
  simp [iterationRun]

-- Fold charging follows the changing accumulator. Reusing the initial
-- accumulator's body cost would incorrectly undercount the second iteration.
example : foldWork (fun x acc : Nat => x + acc) (fun _ acc => acc)
    (fun xs acc => xs.length + acc) [2, 4] 1 = 18 := by
  simp [foldWork]

-- Repeated signing requests still occupy the signed-message list, even when
-- each private cache has only one entry. The invariant works over Nat messages
-- without requiring a finite enumeration of the message type.
example (m : Nat) :
    let state : Coron.CacheState Nat Nat 1 := ⟨[(m, 0)], [(m, 0)], [m, m]⟩
    state.size = 2 ∧ state.Messages (fun x => x = m) := by
  simp [Coron.CacheState.size, Coron.CacheState.Messages]

-- A hit uses no sampling implementation, even in the actual costed compiled
-- program. Replacing every effect therefore preserves both output and time.
example {C : StepClass} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
    {I S Atom : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
    {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type} {key val : Ty Atom}
    (rep : LanguageRepresentation C base) (data : DataCode Q rep.data) (P : Primitives base Op)
    (primitive : {a b : Ty Atom} → (instr : Op a b) →
      Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
    (store : C.Str S)
    (effect otherEffect : {a b : Ty Atom} → Cmd a b →
      Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store) (StepClass.HasProd.prod (rep.ty b) store))
    (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    (eq : Op (.pair key key) .bool) (draw : Cmd .unit val)
    (env : Env base [key, val, .list (.pair key val)]) (saved : S) (value : val.Value base)
    (hlookup : (lookup eq).denote P env = (true, value)) :
    (Language.compile rep data P primitive store effect (cacheGet eq draw)).run control queryCost (env, saved) =
      (Language.compile rep data P primitive store otherEffect (cacheGet eq draw)).run control queryCost (env, saved) := by
  simp only [cacheGet, Language.compile, Language.withContext, Code.run, sequenceRun, retainRun,
    chargeRun, pure_bind, map_pure, hlookup, Expr.denote, Var.get, ite_true]

section CallerExecution

open PFunctor.DynSystem.DynComputation

variable {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption]
  [Q.IsDistributive] [OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
    (StepClass.HasProd.prod bd.idx store))
  (H : GeneralCaller.Handler (spec := source) (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.run control queryCost (i, saved) =
    (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (source.toPFunctor.Idx × S))) <$> (H i).run saved)

-- A query can change both the caller state and the wrapper store. The final
-- stop/readout and zero test use those changed values, and the handler's work
-- appears exactly once even when it is arbitrarily large.
example (state : R.machine.State) (saved saved' : S) (i : I)
    (next : source.Range i → R.machine.State) (reply : source.Range i) (output : B)
    (handlerSteps : Nat) (hv : R.machine.view state = .inr ⟨i, next⟩)
    (hr : (H i).run saved = pure (⟨reply, handlerSteps⟩, saved'))
    (hf : R.machine.view (next reply) = .inl output) :
    (Caller.fromState R store handler 1).run control queryCost (state, saved) =
      pure ⟨(some output, saved'), handlerSteps + Caller.queryWork R store control (state, saved) i reply saved' +
        (Caller.stopWork R store control (next reply, saved') +
          control.loop 0 (Q.size (Caller.frame R store) (next reply, saved'))) +
        control.loop 1 (Q.size (Caller.frame R store) (state, saved))⟩ := by
  rw [Caller.fromState, Code.run, loopRun,
    Caller.body_query_run R store control queryCost handler H hhandler state saved i next hv, hr]
  simp only [map_pure, pure_bind, loopRun]
  rw [Caller.stop_run R store control queryCost]
  simp [chargeRun, hf]

end CallerExecution

end SignaturesTest.BackendAssembly

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Code.run_erase, ``Backend.compile_execute, ``Backend.compile_erase,
      ``Backend.compile_descriptionSize, ``Caller.program_descriptionSize,
      ``Caller.body_query, ``Caller.fromState_denote, ``Caller.program_denote,
      ``Caller.compiled_program_erase, ``Bounds.atomic, ``Bounds.query,
      ``Bounds.seq, ``Bounds.branch, ``Bounds.first, ``Bounds.loop,
      ``Caller.program_bound, ``Caller.compiled_program_bound,
      ``Caller.compiled_program_descriptionSize, ``within_compile,
      ``advantage_le_of_compile, ``iterationRun_erase, ``Bounds.iterate,
      ``Expression.compile, ``Language.repeatDenote_context,
      ``Language.compile_denote, ``Language.compiled_erase,
      ``MachineCompiler.effects_denote, ``MachineCompiler.program_denote,
      ``MachineCompiler.closed_denote, ``MachineCompiler.compiled_closed_erase,
      ``Code.value_mem_denote, ``Coron.backendReply_denote, ``Coron.backendFinish_denote,
      ``Coron.backendReply_cache_bound, ``foldWork_mono, ``foldWork_bound,
      ``Expression.cost_compile_le, ``Expression.cost_arguments_le,
      ``LocalBound.atomic, ``Language.contextInputBound, ``Language.contextReturnBound,
      ``Language.chooseBound, ``Language.loopInputBound, ``Language.loopOutputBound,
      ``Caller.inspect_cost_le, ``Caller.update_cost_le,
      ``SizeLaws.distribute_le, ``SizeLaws.getD_le,
      ``Caller.inspect_cost_of_sizes, ``Caller.update_cost_of_sizes,
      ``Caller.update_cost_of_transition, ``Caller.inspect_cost_of_caps,
      ``Caller.update_cost_of_caps,
      ``Caller.stop_run, ``Caller.body_return_run, ``Caller.body_query_run, ``Caller.program_run,
      ``Caller.fromState_refines_cost, ``Caller.program_refines_cost,
      ``Caller.done_cost_of_width, ``Caller.cutoff_cost_of_width,
      ``Caller.queryArgs_cost_of_width, ``Caller.resumeArgs_cost_of_width,
      ``Caller.routeControl_of_width, ``Caller.inspect_atomic_of_width,
      ``Caller.returnWork_of_width, ``Caller.stopWork_of_width,
      ``Caller.queryWork_of_width, ``Caller.initWork_of_width,
      ``Caller.assembled_bound, ``Caller.assembled_bound_of_width,
      ``Caller.handler_denote_of_run, ``Caller.assembled_within,
      ``Caller.assembled_within_of_width,
      ``ListSizeLaws.size_le_sum, ``ListSizeLaws.size_le_length, ``ListSizeLaws.size_le_cap,
      ``cacheHandler_list_eq, ``cacheHandler_keys, ``Coron.reply_messages,
      ``Coron.machineState_encoded_size, ``Coron.backendReply_state_invariant,
      ``Coron.backendReply_encoded_size, ``LookupCompiler.body_time_bound,
      ``LookupCompiler.lookup_time_bound_of_caps, ``LookupCompiler.lookup_cost_bound,
      ``Coron.scalarLookup_cost, ``Coron.coinLookup_cost,
      ``Language.contextInput_cost_of_width, ``Language.contextReturn_cost_of_width,
      ``Language.withContext_bound_of_width, ``Language.ret_bound_of_width,
      ``Language.bind_bound_of_width, ``Language.query_bound_of_width,
      ``Language.choose_cost_of_width, ``Language.branch_bound_of_width,
      ``CacheCompiler.list_size, ``CacheCompiler.input_size, ``CacheCompiler.output_size,
      ``CacheCompiler.lookup_value_size, ``CacheCompiler.hit_cost, ``CacheCompiler.insert_cost,
      ``CacheCompiler.condition_cost, ``CacheCompiler.cacheGet_bound, ``CacheCompiler.cacheGet_sampling_bound,
      ``Coron.scalarCache_bound, ``Coron.coinCache_bound,
      ``Language.bind_bound_of_width_transition, ``Language.call_bound_of_width,
      ``MachineCompiler.read_bound, ``MachineCompiler.write_bound, ``MachineCompiler.unary_bound,
      ``Coron.extract_cost, ``Coron.signReply_cost, ``Coron.hashReply_cost,
      ``Coron.ReplyCompiler.machineReply_eq, ``Coron.ReplyCompiler.scalarArgs_cost,
      ``Coron.ReplyCompiler.coinArgs_cost, ``Coron.ReplyCompiler.writeState_cost,
      ``Coron.ReplyCompiler.signArgs_cost, ``Coron.ReplyCompiler.hashArgs_cost,
      ``Coron.ReplyCompiler.storeReady_machineState,
      ``Coron.ReplyCompiler.readPre_size, ``Coron.ReplyCompiler.scalarPre_size,
      ``Coron.ReplyCompiler.bothPre_size, ``Coron.ReplyCompiler.writtenPre_size,
      ``Coron.ReplyCompiler.writeState_size, ``Coron.ReplyCompiler.cacheCall_bound,
      ``Coron.ReplyCompiler.scalarCall_bound, ``Coron.ReplyCompiler.coinCall_bound,
      ``Coron.ReplyCompiler.signResult_bound, ``Coron.ReplyCompiler.hashResult_bound,
      ``Coron.ReplyCompiler.backendReply_bound,
      ``MachineCompiler.program_bound_of_unary,
      ``Coron.ReplyCompiler.StateInvariant.ready, ``Coron.ReplyCompiler.backendReply_stateFacts,
      ``Coron.ReplyCompiler.backendReply_invariant_bound, ``Coron.ReplyCompiler.replyProgram_invariant_bound,
      ``Coron.FinishCompiler.machineFinish_eq, ``Coron.FinishCompiler.hashArgs_cost,
      ``Coron.FinishCompiler.lookupArgs_cost, ``Coron.FinishCompiler.extractArgs_cost,
      ``Coron.FinishCompiler.forgery_size, ``Coron.FinishCompiler.startPre_size,
      ``Coron.FinishCompiler.hashPre_size, ``Coron.FinishCompiler.readPre_size,
      ``Coron.FinishCompiler.lookupResult_size, ``Coron.FinishCompiler.lookupPre_size,
      ``Coron.FinishCompiler.backendFinish_bound,
      ``DescriptionSize.castFunction, ``LocalDescriptionLaws.compose_bound,
      ``LocalDescriptionLaws.pair_bound, ``LocalDescriptionLaws.elim_bound,
      ``Expression.variableCode_size, ``Expression.compile_size, ``Expression.arguments_size,
      ``Language.contextInput_size, ``Language.contextReturn_size, ``Language.withContext_descriptionSize,
      ``Language.choose_size, ``Language.loopInput_size, ``Language.loopOutput_size,
      ``Language.compile_descriptionSize, ``MachineCompiler.effects_descriptionSize,
      ``MachineCompiler.program_descriptionSize, ``MachineCompiler.unary_descriptionSize,
      ``MachineCompiler.closed_descriptionSize,
      ``Coron.ReplyCompiler.scalarArgs_description, ``Coron.ReplyCompiler.coinArgs_description,
      ``Coron.ReplyCompiler.writeState_description, ``Coron.ReplyCompiler.signArgs_description,
      ``Coron.ReplyCompiler.hashArgs_description,
      ``Coron.backendReply_descriptionSize, ``Coron.backendFinish_descriptionSize,
      ``IndexedHandler.decode_mk, ``IndexedHandler.repack_decode,
      ``IndexedHandler.handler_run, ``IndexedHandler.matches_of_denote, ``IndexedHandler.handler_erase,
      ``Caller.inspect_descriptionSize, ``Caller.done_descriptionSize,
      ``Caller.queryArgs_descriptionSize, ``Caller.resumeArgs_descriptionSize,
      ``Caller.update_descriptionSize, ``Caller.cutoff_descriptionSize,
      ``Caller.wiringDescriptionSize_bound, ``Caller.program_descriptionSize_bound,
      ``Coron.NativeHandler.group_denote, ``Coron.NativeHandler.random_denote,
      ``Coron.NativeHandler.code_random_denote, ``Coron.NativeHandler.code_hash_denote,
      ``Coron.NativeHandler.code_sign_denote, ``Coron.NativeHandler.code_denote,
      ``Coron.NativeHandler.group_descriptionSize, ``Coron.NativeHandler.random_descriptionSize,
      ``Coron.NativeHandler.code_descriptionSize, ``Coron.NativeHandler.code_sourceHandler,
      ``Coron.NativeHandler.code_executed_run, ``Coron.NativeHandler.executed_erase,
      ``Coron.NativeHandler.caller_denote, ``Coron.NativeHandler.caller_erase,
      ``Caller.fromState_priced_indexed, ``Caller.assembled_bound_indexed,
      ``Caller.assembled_bound_indexed_of_width, ``Caller.assembled_within_indexed_of_width,
      ``firstAtomic_bound_of_width, ``branchStore_bound_of_width,
      ``Coron.ReplyCompiler.StateInvariant.mono,
      ``Coron.NativeHandler.request_size, ``Coron.NativeHandler.random_bound,
      ``Coron.NativeHandler.group_bound, ``Coron.NativeHandler.code_bound,
      ``Coron.NativeHandler.code_stateFacts, ``Coron.NativeHandler.code_stateInvariant,
      ``Coron.NativeHandler.executed_mem_code, ``Coron.NativeHandler.code_reservedState,
      ``Coron.NativeHandler.executed_reserved_bound, ``Coron.NativeHandler.caller_bound,
      ``Coron.NativeSolver.setup_denote, ``Coron.NativeSolver.finishSome_denote,
      ``Coron.NativeSolver.cutoff_denote, ``Coron.NativeSolver.terminal_denote,
      ``Coron.NativeSolver.program_denote, ``Coron.NativeSolver.caller_reference_denote,
      ``Coron.NativeSolver.finish_reference_denote, ``Coron.NativeSolver.program_reference_denote,
      ``Coron.NativeSolver.program_denote_original, ``Coron.NativeSolver.program_erase_original,
      ``Coron.NativeSolver.caller_output_invariant, ``Coron.NativeSolver.caller_output_sizes,
      ``Coron.NativeSolver.setup_descriptionSize, ``Coron.NativeSolver.finishSome_descriptionSize,
      ``Coron.NativeSolver.cutoff_descriptionSize, ``Coron.NativeSolver.terminal_descriptionSize,
      ``Coron.NativeSolver.program_descriptionSize,
      ``Coron.NativeSolver.finishSome_bound, ``Coron.NativeSolver.cutoff_bound,
      ``Coron.NativeSolver.terminal_bound, ``Coron.NativeSolver.input_key_size,
      ``Coron.NativeSolver.initial_reserved, ``Coron.NativeSolver.initial_cost,
      ``Coron.NativeSolver.setup_bound, ``Coron.NativeSolver.program_bound,
      ``Coron.NativeSolver.program_within,
      ``Coron.BoundaryRecovery.canonical, ``Coron.reachable_request,
      ``Coron.reachable_message, ``Coron.resource_step,
      ``Coron.NativeSolver.program_within_of_resources,
      ``Coron.NativeSolver.challenge_size, ``Coron.NativeSolver.security_of_resources,
      ``PolynomiallyBounded.const, ``PolynomiallyBounded.input, ``PolynomiallyBounded.of_le,
      ``PolynomiallyBounded.add, ``PolynomiallyBounded.mul, ``PolynomiallyBounded.comp,
      ``PolynomiallyBounded.sum, ``PolynomialOverhead.apply,
      ``Coron.NativeSolver.nativeSolverTime_polynomial, ``Coron.NativeSolver.description_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
