import Signatures.Runtime.Caliper.WeightedHashLayout

/-! The hash frame is assembled from stored slices. The old request is
retained through lookup and response computation; only the updated cache,
configuration and delivered point survive recording. -/
namespace Signatures.Runtime.CaliperBackend.WeightedHash
open Caliper BoundedSource ByteRoute
variable {w : Nat} {K M R C G : Type} [DecidableEq K] (layout : Layouts w K M R C G)

def requestMessage (value : layout.input.Value) : layout.cache.key.Value := ⟨value.val.1, value.property.1.1⟩
def requestConfig (value : layout.input.Value) : layout.config.Value := ⟨value.val.2.1, value.property.1.2.1⟩
def requestCache (value : layout.input.Value) : layout.cache.lookup.table.Value :=
  ⟨value.val.2.2.1, value.property.1.2.2.1⟩
def requestLogs (value : layout.input.Value) : layout.logs.Value := ⟨value.val.2.2.2, value.property.1.2.2.2⟩

def argument (value : layout.input.Value) : layout.cache.input.Value :=
  ⟨(value.val.1, layout.default.val, value.val.2.2.1, ()),
    ⟨value.property.1.1, layout.default.property, value.property.1.2.2.1, trivial⟩, value.property.2.1⟩

def prepareValue (value : layout.input.Value) :=
  (argument layout value, value)

def prepareParts : List (Part w) :=
  [.slice 0 layout.cache.key.representation.encoding.words,
    .literal (layout.cache.value.representation.encoding.encode layout.default),
    .slice (layout.cache.key.representation.encoding.words + layout.config.representation.encoding.words)
      layout.cache.lookup.table.representation.encoding.words,
    .slice 0 layout.input.representation.encoding.words]
theorem prepareParts_valid :
    ByteRoute.Valid layout.input.representation.encoding.words (prepareParts layout) := by
  change (0 + _ ≤ _) ∧ (_ + _ + _ ≤ _) ∧ (0 + _ ≤ _) ∧ True
  change (0 + _ ≤ _ + (_ + (_ + (layout.hashWords + layout.signWords)))) ∧
    (_ + _ + _ ≤ _ + (_ + (_ + (layout.hashWords + layout.signWords)))) ∧ _ ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepareParts_words :
    ByteRoute.words (prepareParts layout) = layout.prepared.encoding.words := by
  simp only [prepareParts, ByteRoute.words, Encoding.encode_length]
  change _ + (_ + (_ + (_ + 0))) = (_ + (_ + (_ + 0))) + _
  dsimp only [CacheLayout.lookup]
  omega

theorem prepare_bytes (value : layout.input.Value) :
    ByteRoute.bytes (layout.input.representation.encoding.encode value) (prepareParts layout) =
      layout.prepared.encoding.encode (prepareValue layout value) := by
  let m := layout.cache.key.representation.encoding.encode (requestMessage layout value)
  let c := layout.config.representation.encoding.encode (requestConfig layout value)
  let t := layout.cache.lookup.table.representation.encoding.encode (requestCache layout value)
  let logs := layout.logs.representation.encoding.encode (requestLogs layout value)
  have hm : m.length = layout.cache.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : c.length = layout.config.representation.encoding.words := Encoding.encode_length _ _
  have ht : t.length = layout.cache.lookup.table.representation.encoding.words := Encoding.encode_length _ _
  have all : (m ++ (c ++ (t ++ logs))).length = layout.input.representation.encoding.words :=
    layout.input.representation.encoding.encode_length value
  have messageRead := ByteRoute.slice_block [] m (c ++ (t ++ logs))
  have cacheRead := ByteRoute.slice_block (m ++ c) t logs
  simp only [List.nil_append, List.length_nil, List.length_append, hm, hc, ht, List.append_assoc] at messageRead cacheRead
  change ((m ++ (c ++ (t ++ logs))).drop 0).take _ ++
    (_ ++ (((m ++ (c ++ (t ++ logs))).drop (_ + _)).take _ ++
      (((m ++ (c ++ (t ++ logs))).drop 0).take _ ++ []))) = _
  rw [messageRead, cacheRead, ← all]
  simp only [List.drop_zero, List.take_length, List.append_nil]
  change _ = (m ++ (layout.cache.value.representation.encoding.encode layout.default ++ (t ++ []))) ++
    (m ++ (c ++ (t ++ logs)))
  simp only [List.append_assoc, List.append_nil]

def prepare :
    Realizer .unit layout.input.representation layout.prepared (prepareValue layout) :=
  ByteRoute.realizer _ _ _ (prepareParts layout) layout.cache.wordFits
    (prepareParts_valid layout) (prepareParts_words layout) (prepare_bytes layout)

def responseValue (value : layout.evaluated.Value × layout.input.Value) : layout.responseInput.Value :=
  ⟨(value.1.val.1, value.2.val.2.1), value.1.property.1, value.2.property.1.2.1⟩
def responsePrepareValue (value : layout.evaluated.Value × layout.input.Value) := (responseValue layout value, value)
def responseParts : List (Part w) :=
  [.slice 0 layout.cache.value.representation.encoding.words,
    .slice (layout.cache.value.representation.encoding.words +
      layout.cache.lookup.table.representation.encoding.words + layout.cache.key.representation.encoding.words)
      layout.config.representation.encoding.words,
    .slice 0 layout.post.encoding.words]
theorem responseParts_valid : ByteRoute.Valid layout.post.encoding.words (responseParts layout) := by
  change (0 + _ ≤ (_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ∧
    (_ + _ + _ + _ ≤ (_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ∧ (0 + _ ≤ _) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem responseParts_words : ByteRoute.words (responseParts layout) = layout.responsePrepared.encoding.words := by
  change _ + (_ + (_ + 0)) = (_ + _) + _
  omega
theorem response_bytes (value : layout.evaluated.Value × layout.input.Value) :
    ByteRoute.bytes (layout.post.encoding.encode value) (responseParts layout) =
      layout.responsePrepared.encoding.encode (responsePrepareValue layout value) := by
  let r := layout.cache.value.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let t := layout.cache.lookup.table.representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let m := layout.cache.key.representation.encoding.encode (requestMessage layout value.2)
  let c := layout.config.representation.encoding.encode (requestConfig layout value.2)
  let old := layout.cache.lookup.table.representation.encoding.encode (requestCache layout value.2)
  let logs := layout.logs.representation.encoding.encode (requestLogs layout value.2)
  have hr : r.length = layout.cache.value.representation.encoding.words := Encoding.encode_length _ _
  have ht : t.length = layout.cache.lookup.table.representation.encoding.words := Encoding.encode_length _ _
  have hm : m.length = layout.cache.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : c.length = layout.config.representation.encoding.words := Encoding.encode_length _ _
  have all : ((r ++ t) ++ (m ++ (c ++ (old ++ logs)))).length = layout.post.encoding.words :=
    layout.post.encoding.encode_length value
  have scalarRead := ByteRoute.slice_block [] r (t ++ (m ++ (c ++ (old ++ logs))))
  have configRead := ByteRoute.slice_block (r ++ t ++ m) c (old ++ logs)
  simp only [List.nil_append, List.length_nil, List.length_append, hr, ht, hm, hc, List.append_assoc] at scalarRead configRead
  change (((r ++ t) ++ (m ++ (c ++ (old ++ logs)))).drop 0).take _ ++
    ((((r ++ t) ++ (m ++ (c ++ (old ++ logs)))).drop (_ + _ + _)).take _ ++
      ((((r ++ t) ++ (m ++ (c ++ (old ++ logs)))).drop 0).take _ ++ [])) = _
  rw [← all]
  simp only [List.drop_zero, List.take_length, List.append_nil, List.append_assoc]
  simp only [Nat.add_assoc]
  rw [show (r ++ (t ++ (m ++ (c ++ (old ++ logs))))).take _ = r from scalarRead, configRead]
  change _ = (r ++ c) ++ ((r ++ t) ++ (m ++ (c ++ (old ++ logs))))
  simp only [List.append_assoc]
def responsePrepare : Realizer .unit layout.post layout.responsePrepared (responsePrepareValue layout) :=
  ByteRoute.realizer _ _ _ (responseParts layout) layout.cache.wordFits
    (responseParts_valid layout) (responseParts_words layout) (response_bytes layout)

def recordValue (value : layout.point.Value × (layout.evaluated.Value × layout.input.Value)) :
    layout.recorder.leftInput.Value :=
  ⟨((value.2.2.val.1, value.1.val), value.2.2.val.2.2.2),
    ⟨⟨value.2.2.property.1.1, value.1.property⟩, value.2.2.property.1.2.2.2⟩, value.2.2.property.2.2⟩
def savedValue (value : layout.point.Value × (layout.evaluated.Value × layout.input.Value)) :
    layout.saved.Value :=
  ⟨(value.1.val, value.2.2.val.2.1, value.2.1.val.2),
    value.1.property, value.2.2.property.1.2.1, value.2.1.property.2⟩
def recordPrepareValue (value : layout.point.Value × (layout.evaluated.Value × layout.input.Value)) :=
  (recordValue layout value, savedValue layout value)
def messageOffset := layout.point.representation.encoding.words + layout.evaluated.representation.encoding.words
def configOffset := messageOffset layout + layout.cache.key.representation.encoding.words
def logsOffset := configOffset layout + layout.config.representation.encoding.words +
  layout.cache.lookup.table.representation.encoding.words
def recordParts : List (Part w) :=
  [.slice (messageOffset layout) layout.cache.key.representation.encoding.words,
    .slice 0 layout.point.representation.encoding.words,
    .slice (logsOffset layout) layout.logs.representation.encoding.words,
    .slice 0 layout.point.representation.encoding.words,
    .slice (configOffset layout) layout.config.representation.encoding.words,
    .slice (layout.point.representation.encoding.words + layout.cache.value.representation.encoding.words)
      layout.cache.lookup.table.representation.encoding.words]
theorem recordParts_valid : ByteRoute.Valid layout.frame.encoding.words (recordParts layout) := by
  change (_ + (_ + _) + _ ≤ _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧
    (0 + _ ≤ _) ∧
    (_ + (_ + _) + _ + _ + _ + (layout.hashWords + layout.signWords) ≤
      _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧
    (0 + _ ≤ _) ∧ (_ + (_ + _) + _ + _ ≤ _) ∧ (_ + _ + _ ≤ _) ∧ True
  change _ ∧ (0 + _ ≤ _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧ _ ∧
    (0 + _ ≤ _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧
    (_ ≤ _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧
    (_ ≤ _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))))) ∧ True
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
omit [DecidableEq K] in
theorem recordParts_words : ByteRoute.words (recordParts layout) = layout.recordPrepared.encoding.words := by
  change _ + (_ + ((layout.hashWords + layout.signWords) + (_ + (_ + (_ + 0))))) =
    ((_ + _) + (layout.hashWords + layout.signWords)) + (_ + (_ + _))
  omega
theorem record_bytes (value : layout.point.Value × (layout.evaluated.Value × layout.input.Value)) :
    ByteRoute.bytes (layout.frame.encoding.encode value) (recordParts layout) =
      layout.recordPrepared.encoding.encode (recordPrepareValue layout value) := by
  let g := layout.point.representation.encoding.encode value.1
  let r := layout.cache.value.representation.encoding.encode ⟨value.2.1.val.1, value.2.1.property.1⟩
  let t := layout.cache.lookup.table.representation.encoding.encode ⟨value.2.1.val.2, value.2.1.property.2⟩
  let m := layout.cache.key.representation.encoding.encode (requestMessage layout value.2.2)
  let c := layout.config.representation.encoding.encode (requestConfig layout value.2.2)
  let old := layout.cache.lookup.table.representation.encoding.encode (requestCache layout value.2.2)
  let logs := layout.logs.representation.encoding.encode (requestLogs layout value.2.2)
  have hg : g.length = layout.point.representation.encoding.words := Encoding.encode_length _ _
  have hr : r.length = layout.cache.value.representation.encoding.words := Encoding.encode_length _ _
  have ht : t.length = layout.cache.lookup.table.representation.encoding.words := Encoding.encode_length _ _
  have hm : m.length = layout.cache.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : c.length = layout.config.representation.encoding.words := Encoding.encode_length _ _
  have ho : old.length = layout.cache.lookup.table.representation.encoding.words := Encoding.encode_length _ _
  have hl : logs.length = layout.logs.representation.encoding.words := Encoding.encode_length _ _
  have pointRead := ByteRoute.slice_block [] g (r ++ t ++ m ++ c ++ old ++ logs)
  have messageRead := ByteRoute.slice_block (g ++ (r ++ t)) m (c ++ old ++ logs)
  have logsRead := ByteRoute.slice_block ((g ++ (r ++ t)) ++ m ++ c ++ old) logs []
  have configRead := ByteRoute.slice_block ((g ++ (r ++ t)) ++ m) c (old ++ logs)
  have cacheRead := ByteRoute.slice_block (g ++ r) t (m ++ c ++ old ++ logs)
  simp only [List.nil_append, List.append_nil, List.length_nil, List.length_append,
    hg, hr, ht, hm, hc, ho, hl, List.append_assoc] at pointRead messageRead logsRead configRead cacheRead
  change _ = ((m ++ g) ++ logs) ++ (g ++ (c ++ t))
  change ByteRoute.bytes (g ++ ((r ++ t) ++ (m ++ (c ++ (old ++ logs))))) (recordParts layout) = _
  simp only [recordParts, ByteRoute.bytes, messageOffset, configOffset, logsOffset, List.append_assoc]
  change ((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop (_ + (_ + _))).take _ ++
    (((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop 0).take _ ++
    (((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop (_ + (_ + _) + _ + _ + _)).take _ ++
    (((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop 0).take _ ++
    (((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop (_ + (_ + _) + _)).take _ ++
    (((g ++ (r ++ (t ++ (m ++ (c ++ (old ++ logs)))))).drop (_ + _)).take _ ++ []))))) = _
  simp only [Nat.add_assoc] at messageRead configRead logsRead ⊢
  rw [messageRead, pointRead, logsRead, configRead, cacheRead]
  simp only [List.append_nil]

def recordPrepare : Realizer .unit layout.frame layout.recordPrepared (recordPrepareValue layout) :=
  ByteRoute.realizer _ _ _ (recordParts layout) layout.cache.wordFits
    (recordParts_valid layout) (recordParts_words layout) (record_bytes layout)

def finishValue (value : layout.logs.Value × layout.saved.Value) : layout.output.Value :=
  ⟨(value.2.val.1, value.2.val.2.1, value.2.val.2.2, value.1.val),
    value.2.property.1, value.2.property.2.1, value.2.property.2.2, value.1.property⟩
def finish : Realizer .unit layout.recorded layout.output.representation (finishValue layout) :=
  (Pairing.swap .unit (by decide) layout.logs.representation layout.saved.representation
    layout.cache.wordFits layout.recorded.fits).viewOutput layout.output.representation
    (finishValue layout) (by
      intro value
      change _ ++ (_ ++ (_ ++ _)) = (_ ++ (_ ++ _)) ++ _
      simp only [List.append_assoc]
      rfl)

end Signatures.Runtime.CaliperBackend.WeightedHash
