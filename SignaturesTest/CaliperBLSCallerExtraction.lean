import Signatures.Runtime.Caliper.BLSCallerExtractionResources
import Signatures.Runtime.Caliper.BLSCallerExtractionSource
import Signatures.Runtime.Caliper.BLSExtractorAcceptance
import Signatures.Runtime.Caliper.BLSExtractorSource
import Signatures.Runtime.Caliper.BLSInitialization
import Signatures.Runtime.Caliper.BLSFullResources
import Signatures.Runtime.Caliper.BLSFullEquivalence
import Signatures.Runtime.Caliper.BLSFullSecurity
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperBLSCallerExtraction
-- Word arithmetic tests executed composition; it is not a finite-field model.
private def base (_ : Unit) : Type := Word 32
private instance : SampleableType (Ty.Value base (.atom ())) := inferInstanceAs (SampleableType (Word 32))
private instance (n : Nat) : OfNat (Ty.Value base (.atom ())) n := inferInstanceAs (OfNat (Word 32) n)
private instance : Zero (Ty.Value base (.atom ())) := inferInstanceAs (Zero (Word 32))
private instance : Mul (Ty.Value base (.atom ())) := inferInstanceAs (Mul (Word 32))
private instance : Add (Ty.Value base (.atom ())) := inferInstanceAs (Add (Word 32))
private instance : Sub (Ty.Value base (.atom ())) := inferInstanceAs (Sub (Word 32))
private instance : Neg (Ty.Value base (.atom ())) := inferInstanceAs (Neg (Word 32))
private instance : Div (Ty.Value base (.atom ())) := inferInstanceAs (Div (Word 32))
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
private def comparison : Expr Op [.nat, .nat] .bool := .op .equal (.pair (.var .here) (.var (.there .here)))
private theorem comparison_correct (left right : Nat) : comparison.denote primitives (left, right, ()) = decide (left = right) := rfl

private def accumulation : BLSPrivateAccumulate.Layouts 32 Nat (Word 32) where
  cache := {
    key := Layout.counter 32 4294967296 (by decide) (by decide)
    value := Layout.all (wordRepresentation 32 (by decide))
    capacityPred := 4
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  pairStorageFits := by decide
  scalarStorageFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide

private def binary (op : BinOp) : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op accumulation.cache.wordFits).viewInput accumulation.arithmetic.pair.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput accumulation.cache.value.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 * value.2) := binary .mul
private def add : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 + value.2) := binary .add
private theorem mul_bound : mul.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem mul_names : NamesBound mul.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 4 < 2 ^ 32 := by decide

private def rows : BLSRows.Layouts 32 Nat (Word 32) (Word 32) where
  accumulation := accumulation
  point := Layout.all (wordRepresentation 32 (by decide))
  goodStorageFits := by decide
  badStorageFits := by decide
private def layout : BLSTokens.Layouts 32 Nat (Word 32) (Word 32) where
  rows := rows
  capacity := 3
  coefficients := 4
  counterFits := by decide
  coefficientCountFits := by decide
  goodStorageFits := by decide
  badStorageFits := by decide
private def sub : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 - value.2) := binary .sub
private def divide : Implementation .unit accumulation.arithmetic.pair accumulation.cache.value (fun value => value.1 / value.2) := binary .udiv
private def zero : Implementation .unit accumulation.cache.value accumulation.cache.value (fun _ => 0) :=
  Implementation.constant accumulation.cache.value accumulation.cache.value ⟨0, trivial⟩ accumulation.cache.wordFits
private def negArgs : Implementation .unit accumulation.cache.value accumulation.arithmetic.pair (fun value => (0, value)) :=
  zero.pair (Implementation.identity accumulation.cache.value (by decide)) (by decide) accumulation.cache.wordFits
    (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
private def negate : Implementation .unit accumulation.cache.value accumulation.cache.value Neg.neg :=
  (negArgs.then sub).castFunction (by funext value; exact BitVec.zero_sub value)
private theorem sub_bound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem div_bound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem neg_bound : negate.BoundedBy 118 631 := by
  have zeroBound := Implementation.constant_bounded accumulation.cache.value accumulation.cache.value ⟨0, trivial⟩ accumulation.cache.wordFits
  have paired : negArgs.BoundedBy 112 603 := by
    apply (Implementation.pair_boundedBy zero (Implementation.identity accumulation.cache.value (by decide))
      accumulation.cache.wordFits (by decide) (by decide) (by decide) (by decide) accumulation.arithmetic.pair.representation.fits
      zeroBound (Implementation.identity_boundedBy accumulation.cache.value (by decide))).mono <;> decide
  apply ((paired.then sub_bound).castFunction _).mono <;> decide
private theorem sub_names : NamesBound sub.program.code 3 := by constructor <;> decide
private theorem div_names : NamesBound divide.program.code 3 := by constructor <;> decide
private theorem neg_names : NamesBound negate.program.code 3 := by constructor <;> decide


private def port := UniformQuery.port (w := 32) 4294967295 (by decide) (by decide)
private def drawRequest : Realizer .unit accumulation.cache.lookup.unit.representation port.request
    (fun _ => (4294967295 : Fin 4294967296)) :=
  (Implementation.constant accumulation.cache.lookup.unit (Layout.all port.request)
    ⟨(4294967295 : Fin 4294967296), trivial⟩ (by decide)).program.viewOutput
      port.request (fun _ => (4294967295 : Fin 4294967296)) (fun _ => rfl)
private def drawValue (value : UniformQuery.Reply 4294967295) : accumulation.cache.value.Value :=
  ⟨BitVec.ofFin ⟨value.2.val, by have := value.1.isLt; have := value.2.isLt; omega⟩, trivial⟩
private def drawReply : Realizer .unit port.reply accumulation.cache.value.representation drawValue :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (by
    intro value
    change [BitVec.ofNat 32 (drawValue value).val.toNat] = [(drawValue value).val]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])
private def draw : Interactive.Code 32 := .seq (.compute drawRequest.code) (.seq .query (.compute drawReply.code))
private def drawSource : ProbComp accumulation.cache.value.Value := drawValue <$> UniformQuery.source 4294967295 4294967295
private theorem draw_correct : Interactive.Refines port .unit accumulation.cache.lookup.unit.representation accumulation.cache.value.representation
    (fun _ => drawSource) draw := by
  have composed := (Interactive.Refines.compute port .unit drawRequest).seq
    ((UniformQuery.refines 4294967295 (by decide) (by decide)).seq (Interactive.Refines.compute port .unit drawReply))
  convert composed using 1 <;> rfl
private theorem draw_law : Subtype.val <$> drawSource = ($ᵗ (Word 32) : ProbComp (Word 32)) := by
  simp only [drawSource, UniformQuery.source, Functor.map_map]
  rfl
private theorem draw_time : Interactive.TimeBound port .unit accumulation.cache.lookup.unit.representation draw 26 := by
  have first := Interactive.TimeBound.compute (port := port) (cost := .unit) drawRequest 8
    (fun value => (Implementation.constant_bounded accumulation.cache.lookup.unit (Layout.all port.request)
      ⟨(4294967295 : Fin 4294967296), trivial⟩ (by decide)).time_le value)
  have last := Interactive.TimeBound.compute (port := port) (cost := .unit) drawReply 8
    (by intro value; change (selectSlice (w := 32) 1 1).staticTime .unit ≤ 8; decide)
  exact first.seq (Interactive.Refines.compute port .unit drawRequest)
    ((UniformQuery.time_bound 4294967295 (by decide) (by decide)).seq (UniformQuery.refines 4294967295 (by decide) (by decide)) last)
private theorem draw_words : (draw.lower port).descriptionWords ≤ 200 := by decide
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  .seq (by decide) (.compute drawRequest.description_fits)
    (.seq (by decide) (UniformQuery.descriptionFits 4294967295 (by decide) (by decide)) (.compute drawReply.description_fits))

private def goodService := BLSCallerFinish.service layout.good accumulation.cache.lookup.unit (by decide) (by decide)
private def requestRep := BLSCallerPackets.request goodService 4294967295 (by decide)
private def goodLayout : BLSCallerExtraction.Layouts 32 Nat (Word 32) (Word 32) (Word 32) Unit (BLSCallerPackets.Request goodService 4294967295) where
  extraction := layout.good
  config := accumulation.cache.lookup.unit
  positive := by decide
  serviceFits := by decide
  randomBound := 4294967295
  randomFits := by decide
  state := requestRep
  callerFits := by decide
private def badLayout : BLSCallerExtraction.Layouts 32 Nat (Word 32) (Word 32) (Word 32 × Word 32) Unit (BLSCallerPackets.Request goodService 4294967295) where
  extraction := layout.bad
  config := accumulation.cache.lookup.unit
  positive := by decide
  serviceFits := by decide
  randomBound := 4294967295
  randomFits := by decide
  state := requestRep
  callerFits := by decide

private def forgery : goodLayout.forgery.Value := ⟨(5, 20, [2], [3]), by
  exact ⟨by change 5 < 4294967296; decide, trivial,
    ⟨by decide, by intro _ _; trivial⟩, ⟨by decide, by intro _ _; trivial⟩⟩⟩
private def initial (q : goodLayout.Request) : goodLayout.forgery.Value ⊕ (goodLayout.Request × goodLayout.Request) := .inr (q, q)
private def initialCode : Realizer .unit requestRep (CallerStep.next goodLayout.control) initial :=
  ((duplicateRealizer .unit (by decide) requestRep (by decide) (by decide)).then
    (inrRealizer .unit (by decide) goodLayout.forgery.representation (CallerStep.pending goodLayout.control)
      (by decide) (by decide))).viewOutput (CallerStep.next goodLayout.control) initial (fun _ => rfl)
private def randomMessage (value : UniformQuery.Reply 4294967295) : accumulation.cache.key.Value :=
  ⟨value.2.val, by change value.2.val < 4294967296; have := value.1.isLt; have := value.2.isLt; omega⟩
private def messageCode : Realizer .unit port.reply accumulation.cache.key.representation randomMessage :=
  selectSliceRealizer .unit (by decide) _ _ _ 1 (by decide) (by decide) (fun _ => rfl)
private def hashCode := (messageCode.then
  (inlRealizer .unit (by decide) accumulation.cache.key.representation accumulation.cache.key.representation (by decide) (by decide))).then
    (inrRealizer .unit (by decide) port.request
      (accumulation.cache.key.representation.sum accumulation.cache.key.representation (by decide) (by decide)) (by decide) (by decide))
private def returnedCode := (Implementation.constant rows.point goodLayout.forgery forgery (by decide)).program.then
  (inlRealizer .unit (by decide) goodLayout.forgery.representation (CallerStep.pending goodLayout.control) (by decide) (by decide))
private def advance (value : goodLayout.Request × goodLayout.Reply) :=
  match value.2 with
  | .inl random => initial (.inr (.inl (randomMessage random)))
  | .inr _ => .inl forgery
private def continuation : Realizer .unit (CallerStep.resume goodLayout.control) (CallerStep.next goodLayout.control) advance :=
  ((secondRealizer .unit (by decide) requestRep (BLSCallerPackets.reply goodService 4294967295 (by decide)) (by decide) (by decide)).then
    (branchRealizer .unit (by decide) port.reply rows.point.representation (CallerStep.next goodLayout.control)
      (hashCode.then initialCode) returnedCode (by decide) (by decide))).viewOutput (CallerStep.next goodLayout.control) advance (by
        rintro ⟨pending, random | point⟩ <;> rfl)

-- Normalize the executable trees separately from their representation proofs.
private def initialRaw : Stmt 32 :=
  Assembly.code (Assembly.reads 0 0 3 ++ Assembly.reads 0 0 3) ;;
    Assembly.code (Construction.taggedOperands 1 6 6)
private def returnedRaw : Stmt 32 :=
  Assembly.code (([5, 20, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0] : List (Word 32)).map Assembly.Operand.literal) ;;
    Assembly.code (Construction.taggedOperands 0 12 0)
private def continuationRaw : Stmt 32 :=
  selectSlice 3 3 ;; Dispatch.code
    (((selectSlice 1 1 ;; Assembly.code (Construction.taggedOperands 0 1 0)) ;;
      Assembly.code (Construction.taggedOperands 1 2 0)) ;; initialRaw)
    returnedRaw 2 1
private theorem initial_code : initialCode.code = initialRaw := rfl
private theorem continuation_code : continuation.code = continuationRaw := rfl
private theorem initial_words : descriptionWords initialCode.code ≤ 1000 := by
  have copied := Assembly.code_descriptionWords_le (Assembly.reads (w := 32) 0 0 3 ++ Assembly.reads 0 0 3)
  have tagged := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 1 6 6)
  simp only [List.length_append, Assembly.reads_length, Construction.prefix_length] at copied tagged
  rw [initial_code, initialRaw, descriptionWords_seq]
  omega
private theorem continuation_words : descriptionWords continuation.code ≤ 5000 := by
  have init := initial_words
  rw [initial_code] at init
  have first := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 0 1 0)
  have second := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 1 2 0)
  have last := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 0 12 0)
  have literals := Assembly.code_descriptionWords_le (([5, 20, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0] : List (Word 32)).map Assembly.Operand.literal)
  simp only [Construction.prefix_length] at first second last
  simp only [List.length_map, List.length_cons, List.length_nil] at literals
  simp only [continuation_code, continuationRaw, returnedRaw, descriptionWords_seq,
    Dispatch.code_descriptionWords, selectSlice_descriptionWords]
  omega
private theorem initial_names : NamesAccounted initialCode.code 5 := by
  rw [initial_code]
  exact (Assembly.code_namesAccounted _ 5 ((Assembly.sourcesBound_append _ _ _).mpr
    ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).seq
      (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))
private theorem continuation_names : NamesAccounted continuation.code 5 := by
  rw [continuation_code]
  have init : NamesAccounted initialRaw 5 := by simpa only [initial_code] using initial_names
  have returned : NamesAccounted returnedRaw 5 :=
    (Implementation.constant_names rows.point goodLayout.forgery forgery (by decide) 5).seq
      (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))
  exact (selectSlice_names 3 3 5).seq (Dispatch.names
    ((((selectSlice_names 1 1 5).seq (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))).seq
      (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))).seq init)
    returned 2 1)
private theorem initial_name_fits : initialCode.savedBuffer < 2 ^ 32 := by
  have bound := initial_names.buffers
  have words := initial_words
  change max 2 initialCode.code.memBound < 2 ^ 32
  omega
private theorem continuation_name_fits : continuation.savedBuffer < 2 ^ 32 := by
  have bound := continuation_names.buffers
  have words := continuation_words
  change max 2 continuation.code.memBound < 2 ^ 32
  omega

private def responseGood : Implementation .unit goodLayout.service.responseInput rows.point (fun value => value.1) :=
  Implementation.first (cost := .unit) (by decide) accumulation.cache.value accumulation.cache.lookup.unit (by decide) (by decide)
private def responseBad : Implementation .unit badLayout.service.responseInput rows.point (fun value => value.1.1) :=
  (Implementation.first (cost := .unit) (by decide) badLayout.service.cache.value accumulation.cache.lookup.unit (by decide) (by decide)).then
    (Implementation.first (cost := .unit) (by decide) accumulation.cache.value accumulation.cache.value (by decide) (by decide))
private theorem response_good_bound : responseGood.BoundedBy 8 40 := Implementation.first_boundedBy _ _ _ _
private theorem response_bad_bound : responseBad.BoundedBy 24 107 := by
  exact (Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)
private theorem response_good_names : NamesBound responseGood.program.code 3 := by constructor <;> decide
private theorem response_bad_names : NamesBound responseBad.program.code 3 := by constructor <;> decide

private def goodExtractor := BLSExtractor.goodCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw
private def badExtractor := BLSExtractor.badCode (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw
private def goodDenote := BLSExtractor.goodDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers drawSource
private theorem good_correct : Interactive.RefinesOn (BLSExtractor.goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation
    (CacheScalarResult.output accumulation.good).representation goodDenote goodExtractor :=
  BLSExtractor.good_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct
private theorem good_time : Interactive.TimeBoundOn (BLSExtractor.goodReady layout) port .unit (BLSExtractorFrame.input layout.good).representation goodExtractor
    (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 26 6 6 6 6) :=
  BLSExtractor.good_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound div_bound
private theorem good_stored : (goodExtractor.lower port).descriptionWords ≤ BLSExtractor.goodWords (base := base) (key := .nat) (val := .atom ()) layout 200 27 27 27 27 :=
  BLSExtractor.good_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_words mul_bound add_bound sub_bound div_bound
private theorem good_accounted : WordIO.NamesAccounted (goodExtractor.lower port) 5 :=
  BLSExtractor.good_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted div_names.accounted
private theorem good_fits : (goodExtractor.lower port).DescriptionFits :=
  BLSExtractor.good_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub divide mul_names.buffers add_names.buffers sub_names.buffers reserve div_names.buffers port draw draw_fits draw_names (by decide)
private def badDenote := BLSExtractor.badDenote (base := base) (key := .nat) (val := .atom ()) (slots := 3)
  layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers drawSource
private theorem bad_correct : Interactive.RefinesOn (BLSExtractor.badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation
    (CacheScalarResult.output accumulation.bad).representation badDenote badExtractor :=
  BLSExtractor.bad_refines (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct
private theorem bad_time : Interactive.TimeBoundOn (BLSExtractor.badReady layout) port .unit (BLSExtractorFrame.input layout.bad).representation badExtractor
    (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 26 6 6 6 118 6) :=
  BLSExtractor.bad_time (base := base) (key := .nat) (val := .atom ()) (slots := 3) (scalar := draw) (source := drawSource)
    layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw_correct draw_time mul_bound add_bound sub_bound neg_bound div_bound
private theorem bad_stored : (badExtractor.lower port).descriptionWords ≤ BLSExtractor.badWords (base := base) (key := .nat) (val := .atom ()) layout 200 27 27 27 631 27 :=
  BLSExtractor.bad_words (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_words mul_bound add_bound sub_bound neg_bound div_bound
private theorem bad_accounted : WordIO.NamesAccounted (badExtractor.lower port) 5 :=
  BLSExtractor.bad_names (drawNames := 3) (names := 3) (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_names mul_names.accounted add_names.accounted sub_names.accounted neg_names.accounted div_names.accounted
private theorem bad_fits : (badExtractor.lower port).DescriptionFits :=
  BLSExtractor.bad_descriptionFits (base := base) (key := .nat) (val := .atom ()) (slots := 3) layout (by trivial) primitives comparison comparison_correct mul add sub negate divide mul_names.buffers add_names.buffers sub_names.buffers reserve neg_names.buffers div_names.buffers port draw draw_fits draw_names (by decide)

private def good (fuel : Nat) := BLSCallerExtraction.program (base := base) (key := .nat) (val := .atom ())
  goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw
  advance continuation continuation_name_fits requestRep initial initialCode initial_name_fits (by decide) fuel ⟨0, trivial⟩ goodExtractor
private def pairDraw := BLSCache.pairSampler (base := base) (key := .nat) (val := .atom ()) accumulation.cache port draw
private def bad (fuel : Nat) := BLSCallerExtraction.program (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
  badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw
  advance continuation continuation_name_fits requestRep initial initialCode initial_name_fits (by decide) fuel ⟨0, trivial⟩ badExtractor
private def goodInput := requestRep.prod goodLayout.service.store.representation (by decide)
private def badInput := requestRep.prod badLayout.service.store.representation (by decide)
private def goodEmpty := BLSInitialization.store goodLayout.service ⟨(), trivial⟩
private def badEmpty := BLSInitialization.store badLayout.service ⟨(), trivial⟩
private def goodBudget (fuel : Nat) := BLSCallerExtraction.timeBudget (base := base) (key := .nat) (val := .atom ())
  goodLayout requestRep.encoding.words 26 (fun _ => 8) 1000 1000 fuel
    (BLSExtractor.goodTime (base := base) (key := .nat) (val := .atom ()) layout 26 6 6 6 6)
private def pairTime := PairSampling.timeBudget accumulation.cache.value accumulation.cache.value 26 26
private def badBudget (fuel : Nat) := BLSCallerExtraction.timeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
  badLayout requestRep.encoding.words pairTime (fun _ => 24) 1000 1000 fuel
    (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 26 6 6 6 118 6)
private theorem initial_time (value) : initialCode.time value ≤ 1000 := by
  change initialCode.time (.inl 0) ≤ 1000
  decide
private theorem continuation_time (value) : continuation.time value ≤ 1000 := by
  rcases value with ⟨pending, random | point⟩
  · change continuation.time (.inl 0, .inl ⟨(0 : Fin 4294967296), (0 : Fin 1)⟩) ≤ 1000
    decide
  · change continuation.time (.inl 0, .inr ⟨0, trivial⟩) ≤ 1000
    decide
private def localDomain (_ : Nat) (value : goodLayout.Request × goodLayout.Request) := value.1 = value.2
private theorem advance_valid (remaining : Nat) (q c) (_ : localDomain (remaining + 1) (q, c))
    (represented) (original) (_ : BLSCallerHandler.replyMatches goodLayout.service goodLayout.randomBound q represented original) :
    BLSCaller.HeadValid goodLayout.service goodLayout.randomBound localDomain remaining (advance (c, represented)) := by
  cases represented with
  | inl random => rfl
  | inr point => trivial
private theorem advance_bad_valid (remaining : Nat) (q c) (_ : localDomain (remaining + 1) (q, c))
    (represented) (original) (_ : BLSCallerHandler.replyMatches badLayout.service badLayout.randomBound q represented original) :
    BLSCaller.HeadValid badLayout.service badLayout.randomBound localDomain remaining (advance (c, represented)) := by
  cases represented with
  | inl random => rfl
  | inr point => trivial
private def pairSource := PairSampling.denote accumulation.cache.value accumulation.cache.value accumulation.cache.pairValueFits drawSource drawSource
private theorem pair_correct : Interactive.Refines port .unit badLayout.service.cache.lookup.unit.representation badLayout.service.cache.value.representation
    (fun _ => pairSource) pairDraw :=
  PairSampling.refines (hw := accumulation.cache.wordFits) (fits := accumulation.cache.pairValueFits) draw_correct draw_correct
private theorem pair_law : Subtype.val <$> pairSource = ($ᵗ (Word 32 × Word 32) : ProbComp (Word 32 × Word 32)) :=
  PairSampling.uniform accumulation.cache.value accumulation.cache.value accumulation.cache.pairValueFits drawSource drawSource draw_law draw_law
private theorem pair_time : Interactive.TimeBound port .unit badLayout.service.cache.lookup.unit.representation pairDraw pairTime :=
  PairSampling.time_bound (hw := accumulation.cache.wordFits) (fits := accumulation.cache.pairValueFits) draw_correct draw_correct draw_time draw_time
private def pairWords := PairSampling.codeBudget accumulation.cache.value accumulation.cache.value 200 200
private theorem pair_words : (pairDraw.lower port).descriptionWords ≤ pairWords :=
  PairSampling.code_bound accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_words draw_words
private theorem pair_names : WordIO.NamesBound (pairDraw.lower port) 4 :=
  PairSampling.names accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_names draw_names
private theorem pair_fits : (pairDraw.lower port).DescriptionFits :=
  PairSampling.descriptionFits accumulation.cache.value accumulation.cache.value accumulation.cache.wordFits accumulation.cache.pairValueFits port draw draw draw_fits draw_fits draw_names (by decide)
private theorem bad_ready_correct : Interactive.RefinesOn (BLSExtractorFrame.ready layout.bad) port .unit (BLSExtractorFrame.input layout.bad).representation
    (CacheScalarResult.output accumulation.bad).representation badDenote badExtractor :=
  fun tape value ready before holds => bad_correct tape value (BLSExtractorFrame.signatureReady_of_ready layout.bad value ready) before holds
private theorem bad_ready_time : Interactive.TimeBoundOn (BLSExtractorFrame.ready layout.bad) port .unit (BLSExtractorFrame.input layout.bad).representation badExtractor
    (BLSExtractor.badTime (base := base) (key := .nat) (val := .atom ()) layout 26 6 6 6 118 6) :=
  fun tape value ready before holds finished reached => bad_time tape value (BLSExtractorFrame.signatureReady_of_ready layout.bad value ready) before holds finished reached

private def goodAdmitted (fuel : Nat) (value : goodLayout.Request × goodLayout.service.store.Value) :=
  BLSReply.Reserved goodLayout.service fuel value.2.val ∧
    value.2.val.2.1.length + value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1 ≤ goodLayout.service.cache.capacityPred + 1
private def goodSource (fuel : Nat) := BLSCallerExtraction.denote (base := base) (key := .nat) (val := .atom ())
  goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide)
  advance initial fuel drawSource ⟨0, trivial⟩ goodDenote
private theorem caller_good_correct (fuel : Nat) : Interactive.RefinesOn (goodAdmitted fuel) port .unit goodInput
    accumulation.cache.value.representation (goodSource fuel) (good fuel) :=
  BLSCallerExtraction.refines (base := base) (key := .nat) (val := .atom ()) goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    drawSource draw_correct draw_law localDomain advance_valid (goodAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2) ⟨0, trivial⟩ good_correct
private theorem caller_good_time (fuel : Nat) : Interactive.TimeBoundOn (goodAdmitted fuel) port .unit goodInput (good fuel) (goodBudget fuel) :=
  BLSCallerExtraction.time (base := base) (key := .nat) (val := .atom ()) goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    drawSource draw_correct draw_law localDomain advance_valid (goodAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2) draw_time (fun _ => response_good_bound) continuation_time initial_time ⟨0, trivial⟩ good_correct good_time
private def goodWords (fuel : Nat) := BLSCallerExtraction.codeBudget (base := base) (key := .nat) (val := .atom ())
  goodLayout requestRep.encoding.words 200 (fun _ => 40) 5000 1000 fuel
    (BLSExtractor.goodWords (base := base) (key := .nat) (val := .atom ()) layout 200 27 27 27 27)
private theorem caller_good_stored (fuel : Nat) : ((good fuel).lower port).descriptionWords ≤ goodWords fuel :=
  BLSCallerExtraction.words (base := base) (key := .nat) (val := .atom ()) goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    draw_words (fun _ => response_good_bound) continuation_words initial_words ⟨0, trivial⟩ good_stored
private theorem caller_good_names (fuel : Nat) : WordIO.NamesAccounted ((good fuel).lower port) 5 :=
  BLSCallerExtraction.names (base := base) (key := .nat) (val := .atom ()) goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    ⟨0, trivial⟩ (by decide) draw_names (fun _ => response_good_names.accounted) (by decide) (by decide) continuation_names initial_names good_accounted
private theorem caller_good_fits (fuel : Nat) : ((good fuel).lower port).DescriptionFits :=
  BLSCallerExtraction.descriptionFits (base := base) (key := .nat) (val := .atom ()) goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide) draw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    draw_words (fun _ => response_good_bound) ⟨0, trivial⟩ draw_fits draw_names (fun _ => response_good_names.accounted) (by decide) good_fits

private def badAdmitted (fuel : Nat) (value : goodLayout.Request × badLayout.service.store.Value) :=
  BLSReply.Reserved badLayout.service fuel value.2.val ∧
    value.2.val.2.1.length + value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1 ≤ badLayout.service.cache.capacityPred + 1
private def badSource (fuel : Nat) := BLSCallerExtraction.denote (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
  badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide)
  advance initial fuel pairSource ⟨0, trivial⟩ badDenote
private theorem caller_bad_correct (fuel : Nat) : Interactive.RefinesOn (badAdmitted fuel) port .unit badInput
    accumulation.cache.value.representation (badSource fuel) (bad fuel) :=
  BLSCallerExtraction.refines (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    pairSource pair_correct pair_law localDomain advance_bad_valid (badAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2) ⟨0, trivial⟩ bad_ready_correct
private theorem caller_bad_time (fuel : Nat) : Interactive.TimeBoundOn (badAdmitted fuel) port .unit badInput (bad fuel) (badBudget fuel) :=
  BLSCallerExtraction.time (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    pairSource pair_correct pair_law localDomain advance_bad_valid (badAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2) pair_time (fun _ => response_bad_bound) continuation_time initial_time ⟨0, trivial⟩ bad_ready_correct bad_ready_time
private def badWords (fuel : Nat) := BLSCallerExtraction.codeBudget (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
  badLayout requestRep.encoding.words pairWords (fun _ => 107) 5000 1000 fuel
    (BLSExtractor.badWords (base := base) (key := .nat) (val := .atom ()) layout 200 27 27 27 631 27)
private theorem caller_bad_stored (fuel : Nat) : ((bad fuel).lower port).descriptionWords ≤ badWords fuel :=
  BLSCallerExtraction.words (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    pair_words (fun _ => response_bad_bound) continuation_words initial_words ⟨0, trivial⟩ bad_stored
private theorem caller_bad_names (fuel : Nat) : WordIO.NamesAccounted ((bad fuel).lower port) 5 :=
  BLSCallerExtraction.names (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    ⟨0, trivial⟩ (by decide) pair_names (fun _ => response_bad_names.accounted) (by decide) (by decide) continuation_names initial_names bad_accounted
private theorem caller_bad_fits (fuel : Nat) : ((bad fuel).lower port).DescriptionFits :=
  BLSCallerExtraction.descriptionFits (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ())) badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct
    (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide) pairDraw advance continuation continuation_name_fits
    requestRep initial initialCode initial_name_fits (by decide) fuel
    pair_words (fun _ => response_bad_bound) ⟨0, trivial⟩ pair_fits pair_names (fun _ => response_bad_names.accounted) (by decide) bad_fits

private theorem good_empty_admitted (fuel : Nat) (small : fuel ≤ 2) (request : goodLayout.Request) :
    goodAdmitted fuel (request, goodEmpty) := by
  refine ⟨BLSInitialization.reserved goodLayout.service fuel (by change fuel ≤ 5; omega) (by change fuel ≤ 3; omega) ⟨(), trivial⟩, ?_⟩
  change 0 + 0 + 0 + 2 * fuel + 1 ≤ 5
  omega
private theorem caller_good_memory (fuel : Nat) (tape : RandomTape 32) (value) (valid : goodAdmitted fuel value)
    (before : State 32) (holds : goodInput.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 32) (reached : some finished ∈ support ((good fuel).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((good fuel).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((good fuel).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((good fuel).lower port).memBound) ≤
          5 * goodWords fuel + 4 * 5 + registers + 3 * buffers + before.liveMem buffers + goodBudget fuel := by
  have certified := BLSCallerExtraction.resources (base := base) (key := .nat) (val := .atom ())
    goodLayout ⟨0, trivial⟩ primitives comparison comparison_correct (fun _ => responseGood) (fun _ => response_good_names.buffers) (by decide)
    draw advance continuation continuation_name_fits requestRep initial initialCode initial_name_fits (by decide) fuel
    drawSource draw_correct draw_law localDomain advance_valid (goodAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2)
    draw_time draw_words (fun _ => response_good_bound) continuation_time initial_time continuation_words initial_words
    ⟨0, trivial⟩ good_correct good_time good_stored (by decide) draw_names (fun _ => response_good_names.accounted)
    (by decide) (by decide) continuation_names initial_names good_accounted tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  exact ⟨execution, fun between visited => (bounded between visited).2.2.2⟩

private theorem bad_empty_admitted (fuel : Nat) (small : fuel ≤ 2) (request : badLayout.Request) :
    badAdmitted fuel (request, badEmpty) := by
  refine ⟨BLSInitialization.reserved badLayout.service fuel (by change fuel ≤ 5; omega) (by change fuel ≤ 3; omega) ⟨(), trivial⟩, ?_⟩
  change 0 + 0 + 0 + 2 * fuel + 1 ≤ 5
  omega
private theorem caller_bad_memory (fuel : Nat) (tape : RandomTape 32) (value) (valid : badAdmitted fuel value)
    (before : State 32) (holds : badInput.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 32) (reached : some finished ∈ support ((bad fuel).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((bad fuel).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((bad fuel).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((bad fuel).lower port).memBound) ≤
          5 * badWords fuel + 4 * 5 + registers + 3 * buffers + before.liveMem buffers + badBudget fuel := by
  have certified := BLSCallerExtraction.resources (base := base) (key := .nat) (val := .pair (.atom ()) (.atom ()))
    badLayout ⟨(0, 0), trivial, trivial⟩ primitives comparison comparison_correct (fun _ => responseBad) (fun _ => response_bad_names.buffers) (by decide)
    pairDraw advance continuation continuation_name_fits requestRep initial initialCode initial_name_fits (by decide) fuel
    pairSource pair_correct pair_law localDomain advance_bad_valid (badAdmitted fuel)
    (fun _ _ => rfl) (fun _ valid => valid.1) (fun _ valid => valid.2)
    pair_time pair_words (fun _ => response_bad_bound) continuation_time initial_time continuation_words initial_words
    ⟨0, trivial⟩ bad_ready_correct bad_ready_time bad_stored (by decide) pair_names (fun _ => response_bad_names.accounted)
    (by decide) (by decide) continuation_names initial_names bad_accounted tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  exact ⟨execution, fun between visited => (bounded between visited).2.2.2⟩

private def run {U : Type} (input : Representation 32 U) (code : Interactive.Code 32) (budget : Nat) (value : U) (replies : List (Word 32)) := do
  let initial := input.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 500000 (code.lower port) before replies
  pure (result.state.bufs 0, result.state.bufs 200, result.state.caps 200, result.state.regs 99, result.state.tapePos,
    (List.range 32).all (fun i => result.state.caps (i + 1) == 0), result.trace, result.remaining, decide (result.time ≤ budget))
private def runGood (fuel : Nat) := run goodInput (good fuel) (goodBudget fuel)
private def runBad (fuel : Nat) := run badInput (bad fuel) (badBudget fuel)
private def hash (message : Fin 4294967296) : goodLayout.Request := .inr (.inl ⟨message.val, message.isLt⟩)
private def sign (message : Fin 4294967296) : goodLayout.Request := .inr (.inr ⟨message.val, message.isLt⟩)
private def events (values : List (Word 32 × Word 32)) : List (WordIO.Event 32) :=
  values.flatMap (fun (bound, value) => [.output bound, .invoke, .input bound, .input value])
private def wire (values : List (Word 32 × Word 32)) : List (Word 32) := values.flatMap (fun (bound, value) => [bound, value])

open Lean in
run_cmd do
  let full : Word 32 := 4294967295
  for (fuel, request, samples, expected) in [
      (1, hash 2, [(full, 5), (full, 10)], 3),
      (1, sign 3, [(full, 5), (full, 25)], 2),
      (2, .inl 3, [(3, 2), (full, 5), (full, 10)], 3),
      (1, hash 5, [(full, 5)], 6),
      (0, hash 2, [], 0),
      (1, .inl 3, [(3, 2)], 0)] do
    unless runGood fuel (request, goodEmpty) (wire samples ++ [88]) ==
        some (#[expected], #[77], 4, 91, 9, true, events samples, [88], true) do
      throwError "composed good caller/extractor failed at fuel {fuel}"
  for (fuel, request, samples, expected) in [
      (1, sign 3, [(full, 5), (full, 2), (full, 17), (full, 2)], 2),
      (1, hash 2, [(full, 5), (full, 2), (full, 7), (full, 0)], 0),
      (2, .inl 3, [(3, 2), (full, 5), (full, 2), (full, 7), (full, 0)], 0),
      (0, sign 3, [], 0),
      (1, .inl 3, [(3, 2)], 0)] do
    unless runBad fuel (request, badEmpty) (wire samples ++ [88]) ==
        some (#[expected], #[77], 4, 91, 9, true, events samples, [88], true) do
      throwError "composed bad caller/extractor failed at fuel {fuel}"
  unless (runGood 1 (hash 2, goodEmpty) [full, 5]).isNone do
    throwError "composed good extractor accepted a missing final scalar"
  unless (runBad 1 (sign 3, badEmpty) [full, 5, full, 2, full, 17]).isNone do
    throwError "composed bad extractor accepted a partial final pair"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSCallerExtraction.Layouts.exitFits, ``BLSCallerExtraction.Layouts.packet_bytes,
      ``BLSCallerExtraction.Layouts.packet_ready, ``BLSCallerExtraction.called_ready, ``BLSCallerExtraction.refines,
      ``BLSCallerExtraction.time, ``BLSCallerExtraction.words, ``BLSCallerExtraction.names,
      ``BLSCallerExtraction.resources, ``BLSCallerExtraction.descriptionFits,
      ``BLSCallerExtraction.finish_source, ``BLSCallerExtraction.called_source,
      ``BLSCallerExtraction.denote_source, ``BLSCallerExtraction.observe_source,
      ``draw_correct, ``draw_law, ``pair_correct, ``pair_law, ``advance_valid, ``advance_bad_valid,
      ``good_empty_admitted, ``bad_empty_admitted, ``good_correct, ``bad_correct,
      ``caller_good_correct, ``caller_bad_correct, ``caller_good_time, ``caller_bad_time,
      ``caller_good_stored, ``caller_bad_stored, ``caller_good_names, ``caller_bad_names,
      ``caller_good_fits, ``caller_bad_fits, ``caller_good_memory, ``caller_bad_memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

-- The complete programs execute setup before the same adaptive caller.
private instance : SMul (Word 32) (Word 32) := ⟨fun scalar point => scalar * point⟩
private instance : SMul (Ty.Value base (.atom ())) (Word 32) := inferInstanceAs (SMul (Word 32) (Word 32))
private def fullLayout : BLSFull.Layouts 32 Nat (Word 32) (Word 32) (Word 32) goodLayout.Request where
  shared := ⟨layout, by decide, by decide, by decide, by decide⟩
  key := rows.point
  setupFits := by decide
  randomBound := 4294967295
  randomFits := by decide
  state := requestRep
  goodCallerFits := by decide
  badCallerFits := by decide
private def fullRoutines : BLSFull.Routines fullLayout where
  zeroValid := trivial
  scalarMul := mul
  scalarAdd := add
  scalarSub := sub
  scalarNeg := negate
  scalarDiv := divide
  groupScale := mul
  groupAdd := add
  keyScale := mul
  slots := 3
  reserve := by decide
  mulNames := mul_names
  addNames := add_names
  subNames := sub_names
  negNames := neg_names
  divNames := div_names
  scaleNames := mul_names
  groupAddNames := add_names
  keyNames := mul_names
private def fullBounds : BLSFull.Routines.Bounds fullLayout fullRoutines where
  mul := ⟨6, 27⟩
  add := ⟨6, 27⟩
  sub := ⟨6, 27⟩
  neg := ⟨118, 631⟩
  divide := ⟨6, 27⟩
  scale := ⟨6, 27⟩
  groupAdd := ⟨6, 27⟩
  key := ⟨6, 27⟩
  mulBound := mul_bound
  addBound := add_bound
  subBound := sub_bound
  negBound := neg_bound
  divBound := div_bound
  scaleBound := mul_bound
  groupAddBound := add_bound
  keyBound := mul_bound

private def keyBound (value : fullLayout.key.Value) : Fin 4294967296 := ⟨value.val.toNat, value.val.isLt⟩
private def keyBoundCode : Realizer .unit fullLayout.key.representation port.request keyBound :=
  (Implementation.identity fullLayout.key (by decide)).program.viewOutput port.request keyBound (by
    intro value
    change [BitVec.ofNat 32 value.val.toNat] = [value.val]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq])
private def keyRequestCode := keyBoundCode.then
  (inlRealizer .unit (by decide) port.request
    (accumulation.cache.key.representation.sum accumulation.cache.key.representation (by decide) (by decide)) (by decide) (by decide))
private def fullInitial (value : fullLayout.key.Value) : fullLayout.Next := initial (.inl (keyBound value))
private def fullInitialCode : Realizer .unit fullLayout.key.representation (CallerStep.next fullLayout.good.control) fullInitial :=
  keyRequestCode.then initialCode
private theorem full_initial_code : fullInitialCode.code =
    (.skip ;; Assembly.code (Construction.taggedOperands 0 1 1)) ;; initialRaw := rfl
private theorem full_initial_words : descriptionWords fullInitialCode.code ≤ 2000 := by
  have old := initial_words
  rw [initial_code] at old
  have tagged := Assembly.code_descriptionWords_le (Construction.taggedOperands (w := 32) 0 1 1)
  simp only [Construction.prefix_length] at tagged
  rw [full_initial_code, descriptionWords_seq, descriptionWords_seq]
  have skip : descriptionWords (.skip : Stmt 32) = 1 := rfl
  rw [skip]
  omega
private theorem full_initial_names : NamesAccounted fullInitialCode.code 5 := by
  rw [full_initial_code]
  exact ((skip_names 5).seq (Assembly.code_namesAccounted _ 5 (Construction.prefix_sources _ _ _))).seq
    (by simpa only [initial_code] using initial_names)
private theorem full_initial_name_fits : fullInitialCode.savedBuffer < 2 ^ 32 := by
  have bounded := full_initial_names.buffers
  have words := full_initial_words
  change max 2 fullInitialCode.code.memBound < 2 ^ 32
  omega
private theorem full_initial_time (value) : fullInitialCode.time value ≤ 2000 := by
  change fullInitialCode.time ⟨0, trivial⟩ ≤ 2000
  decide
private def fullCaller : BLSFull.Caller fullLayout where
  advance := advance
  continuation := continuation
  localNameFits := continuation_name_fits
  initial := fullInitial
  initialCode := fullInitialCode
  initialNameFits := full_initial_name_fits
private def fullCallerBounds : BLSFull.Caller.Bounds fullLayout fullCaller where
  step := ⟨1000, 5000⟩
  initial := ⟨2000, 2000⟩
  localTime := continuation_time
  initialTime := full_initial_time
  localWords := continuation_words
  initialWords := full_initial_words
  names := 5
  localNames := continuation_names
  initialNames := full_initial_names
private def fullInvariant (fuel : Nat) : BLSFull.Caller.Invariant fullLayout fullCaller fuel where
  domain := localDomain
  goodAdvance remaining q c _ represented original _ := by
    cases represented with
    | inl random => rfl
    | inr point => trivial
  badAdvance remaining q c _ represented original _ := by
    cases represented with
    | inl random => rfl
    | inr point => trivial
  initial _ := rfl
private def fullGood (fuel : Nat) := BLSFull.goodCode (base := base) (key := .nat) (val := .atom ())
  fullLayout fullRoutines primitives comparison comparison_correct fullCaller draw fuel
private def fullBad (fuel : Nat) := BLSFull.badCode (base := base) (key := .nat) (val := .atom ())
  fullLayout fullRoutines primitives comparison comparison_correct fullCaller draw fuel
private def fullGoodBudget (fuel : Nat) := BLSFull.goodTime (base := base) (key := .nat) (val := .atom ())
  fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 26 fuel
private def fullBadBudget (fuel : Nat) := BLSFull.badTime (base := base) (key := .nat) (val := .atom ())
  fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 26 fuel
private theorem fullGoodCertificate (tape : RandomTape 32) (value : fullLayout.setup.challenge.Value)
    (before : State 32) (holds : fullLayout.setup.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 32) (reached : some finished ∈ support ((fullGood 2).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((fullGood 2).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((fullGood 2).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((fullGood 2).lower port).memBound) ≤
          5 * BLSFull.goodWords (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 200 2 +
            4 * 5 + registers + 3 * buffers + before.liveMem buffers + fullGoodBudget 2 := by
  have certified := BLSFull.good_resources (base := base) (key := .nat) (val := .atom ())
    fullLayout fullRoutines primitives comparison comparison_correct fullCaller draw 2 drawSource draw_correct
    fullBounds fullCallerBounds draw_time draw_words draw_law (fullInvariant 2) (by decide) (by decide) draw_names
    tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  exact ⟨execution, fun between visited => (bounded between visited).2.2.2⟩
private theorem fullBadCertificate (tape : RandomTape 32) (value : fullLayout.setup.challenge.Value)
    (before : State 32) (holds : fullLayout.setup.challenge.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 32) (reached : some finished ∈ support ((fullBad 2).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((fullBad 2).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((fullBad 2).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((fullBad 2).lower port).memBound) ≤
          5 * BLSFull.badWords (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 200 2 +
            4 * 5 + registers + 3 * buffers + before.liveMem buffers + fullBadBudget 2 := by
  have certified := BLSFull.bad_resources (base := base) (key := .nat) (val := .atom ())
    fullLayout fullRoutines primitives comparison comparison_correct fullCaller draw 2 drawSource draw_correct
    fullBounds fullCallerBounds draw_time draw_words draw_law (fullInvariant 2) (by decide) (by decide) draw_names
    tape value before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  exact ⟨execution, fun between visited => (bounded between visited).2.2.2⟩
private theorem full_addresses : BLSFull.AddressBounds (base := base) (key := .nat) (val := .atom ())
    fullLayout fullRoutines fullBounds 3 200 := by constructor <;> decide
private theorem full_good_fits (fuel : Nat) : ((fullGood fuel).lower port).DescriptionFits :=
  BLSFull.good_fits (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds primitives comparison comparison_correct
    fullCaller draw fuel draw_names draw_words draw_fits full_addresses
private theorem full_bad_fits (fuel : Nat) : ((fullBad fuel).lower port).DescriptionFits :=
  BLSFull.bad_fits (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds primitives comparison comparison_correct
    fullCaller draw fuel draw_names draw_words draw_fits full_addresses
private theorem full_good_within : Interactive.Within fullLayout.port fullLayout.setup.challenge fullLayout.scheme.cache.value
    (BLSFull.goodWords (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 200 2)
    (BLSFull.goodMemory (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 26 200 3 2)
    (fullGoodBudget 2)
    (fun value => Subtype.val <$> BLSFull.goodSource (base := base) (key := .nat) (val := .atom ())
      fullLayout fullRoutines primitives comparison comparison_correct fullCaller 2 drawSource value) :=
  BLSFull.good_within (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds
    primitives comparison comparison_correct draw 2 drawSource draw_correct draw_time draw_words draw_names draw_fits full_addresses
    draw_law (fullInvariant 2) (by decide) (by decide)
private theorem full_bad_within : Interactive.Within fullLayout.port fullLayout.setup.challenge fullLayout.scheme.cache.value
    (BLSFull.badWords (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 200 2)
    (BLSFull.badMemory (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds 26 200 3 2)
    (fullBadBudget 2)
    (fun value => Subtype.val <$> BLSFull.badSource (base := base) (key := .nat) (val := .atom ())
      fullLayout fullRoutines primitives comparison comparison_correct fullCaller 2 drawSource value) :=
  BLSFull.bad_within (base := base) (key := .nat) (val := .atom ()) fullLayout fullRoutines fullBounds fullCaller fullCallerBounds
    primitives comparison comparison_correct draw 2 drawSource draw_correct draw_time draw_words draw_names draw_fits full_addresses
    draw_law (fullInvariant 2) (by decide) (by decide)
private theorem all_challenges_fit (scalar : Word 32) : fullLayout.setup.challenge.valid ((7, scalar • (7 : Word 32)), (3, scalar • (3 : Word 32))) :=
  BLSFull.challenge_valid fullLayout fullRoutines drawSource draw_law ⟨7, trivial⟩ ⟨3, trivial⟩ scalar
private def challenge : fullLayout.setup.challenge.Value := ⟨((7, 11), (3, 3)), by exact ⟨⟨trivial, trivial⟩, trivial, trivial⟩⟩
private def runFullGood (fuel : Nat) := run fullLayout.setup.challenge.representation (fullGood fuel) (fullGoodBudget fuel) challenge
private def runFullBad (fuel : Nat) := run fullLayout.setup.challenge.representation (fullBad fuel) (fullBadBudget fuel) challenge

open Lean in
run_cmd do
  let full : Word 32 := 4294967295
  for (fuel, samples, expected) in [
      (2, [(3, 2), (full, 5), (full, 10)], 3),
      (0, [], 0),
      (1, [(3, 2)], 0)] do
    unless runFullGood fuel (wire samples ++ [88]) ==
        some (#[expected], #[77], 4, 91, 9, true, events samples, [88], true) do
      throwError "complete good BLS program failed at fuel {fuel}"
  -- The sampled setup scalar changes the public key from 3 to 6, and therefore
  -- changes the caller's first random-query bound from 3 to 6.
  for (fuel, samples, expected) in [
      (2, [(full, 2), (6, 2), (full, 5), (full, 2), (full, 7), (full, 0)], 0),
      (0, [(full, 2)], 0),
      (1, [(full, 2), (6, 2)], 0)] do
    unless runFullBad fuel (wire samples ++ [88]) ==
        some (#[expected], #[77], 4, 91, 9, true, events samples, [88], true) do
      throwError "complete bad BLS program failed at fuel {fuel}"
  unless (runFullGood 2 (wire [(3, 2), (full, 5)])).isNone do
    throwError "complete good program accepted a missing final scalar"
  unless (runFullBad 2 (wire [(full, 2), (6, 2), (full, 5), (full, 2), (full, 7)])).isNone do
    throwError "complete bad program accepted a partial final pair"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSFull.good_refines, ``BLSFull.bad_refines, ``BLSFull.good_time, ``BLSFull.bad_time,
      ``BLSFull.good_words, ``BLSFull.bad_words, ``BLSFull.good_names, ``BLSFull.bad_names,
      ``BLSFull.good_fits, ``BLSFull.bad_fits, ``BLSFull.good_resources, ``BLSFull.bad_resources,
      ``BLSCallerHandler.original_run, ``BLSFull.good_extract_original, ``BLSFull.bad_extract_original,
      ``BLSFull.good_tail_original, ``BLSFull.bad_tail_original, ``BLSFull.good_original_finish, ``BLSFull.bad_original_finish,
      ``BLSFull.good_source, ``BLSFull.bad_source, ``BLSFull.good_observe_original, ``BLSFull.bad_observe_original,
      ``fullGoodCertificate, ``fullBadCertificate, ``full_good_fits, ``full_bad_fits,
      ``full_good_within, ``full_bad_within, ``all_challenges_fit, ``BLSFull.good_within, ``BLSFull.bad_within,
      ``BLSFull.scalar_valid, ``BLSFull.challenge_valid, ``BLSFull.good_dlogWithin, ``BLSFull.bad_dlogWithin,
      ``dlogWithin.mono, ``dlogSuccessBound_mono, ``BLSFull.security, ``BLSFull.direct_security] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSCallerExtraction
