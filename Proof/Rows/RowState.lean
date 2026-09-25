import Proof.Rows.Plan

/-!
# Retained, padded row states

The Header bank is common to every row, including the exhausted state. Its raw
source is the full family word and only the source head advances. Every Header
port has an explicit retained reserve. The work bank depends on the row index,
so the physical completion must establish the next key rather than reuse an
unchanging key by definition. An initially empty family retains its public pool
word without constructing unused unary metadata. No execution is asserted by
these bank definitions; `RowReady.ready_body` retains the actual completion Step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowState
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

variable (printer : WilliamsAlgorithm) (work : Nat)

/-! ## 1. The three port blocks -/

/-- A bank built blockwise: Header ports, Frame ports, work ports. -/
def portCases {α : Type} (h : Fin 440 → α)
    (f : Fin (P1TopDownPaidPayload.tapes printer+2) → α) (w : Fin (rowWork work) → α) :
    Fin (rowTapes printer work) → α :=
  Fin.addCases (m:=440+(P1TopDownPaidPayload.tapes printer+2)) (n:=rowWork work)
    (Fin.addCases (m:=440) (n:=P1TopDownPaidPayload.tapes printer+2) h f) w

/-- The `k`-th public/private work port of the row bank. -/
def workSlot (k : Fin (rowWork work)) : Fin (rowTapes printer work) :=
  k.natAdd (440+(P1TopDownPaidPayload.tapes printer+2))

variable {α : Type} (h : Fin 440 → α) (f : Fin (P1TopDownPaidPayload.tapes printer+2) → α)
  (w : Fin (rowWork work) → α)

theorem portCases_header (k : Fin 440) :
    portCases printer work h f w
      (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=h k := by
  simp only [portCases,PCJ38fbfed565f64139_Ready.headerSlots,Fin.addCases_left]

theorem portCases_frame (k : Fin (P1TopDownPaidPayload.tapes printer+2)) :
    portCases printer work h f w
      (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k)=f k := by
  simp only [portCases,PCJ38fbfed565f64139_Ready.frameSlots,Fin.addCases_left,Fin.addCases_right]

theorem portCases_work (k : Fin (rowWork work)) :
    portCases printer work h f w (workSlot printer work k)=w k := by
  simp only [portCases,workSlot,Fin.addCases_right]

/-! ## 2. The three blocks of one row -/

variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (caps : RowCaps) (reserve : Fin 440 → Nat)
  (base : Nat → Fin (rowWork work) → List Bool) (drv lg : Fin (rowWork work))

/-- The full raw source remains resident throughout the family. -/
def rawFamily : List Bool := F.rows.flatMap (PCJ38fbfed565f64139_Family.rawWord a F g)

theorem raw_split (j : Fin F.rows.attach.length) :
    PCJ38fbfed565f64139_Family.rawBefore a F g j.val ++
      PCJ38fbfed565f64139_Family.rawWord a F g
        (PCJ38fbfed565f64139_Family.rowAt F j).val ++
      PCJ38fbfed565f64139_Family.rawAfter a F g j.val = rawFamily a F g := by
  have hj : j.val < F.rows.length := by simpa only [List.length_attach] using j.isLt
  have hr : (PCJ38fbfed565f64139_Family.rowAt F j).val = F.rows[j.val] := by
    simp only [PCJ38fbfed565f64139_Family.rowAt,List.getElem_attach]
  rw [hr]
  unfold PCJ38fbfed565f64139_Family.rawBefore PCJ38fbfed565f64139_Family.rawAfter rawFamily
  have h := congrArg (List.flatMap (PCJ38fbfed565f64139_Family.rawWord a F g))
    (List.take_append_drop j.val F.rows)
  rw [List.drop_eq_getElem_cons hj,List.flatMap_append,List.flatMap_cons] at h
  simpa only [List.append_assoc] using h

/-- Metadata and packet-count driver do not depend on the row key. -/
def commonHeader : Fin 440 → List Bool :=
  letI := PCJcc051fd4c1bd4540_Header.radix a F g layout
  CompactNativeInitialize.input (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (C10SupplierRowInput.liveList (Packets.live F)).length (rawFamily a F g) []

theorem commonHeader_at (j : Fin F.rows.attach.length) :
    commonHeader a F g layout =
      PCJcc051fd4c1bd4540_Header.input a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val []
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) := by
  unfold commonHeader PCJcc051fd4c1bd4540_Header.input
  rw [show ((Packets.packets a F g (PCJ38fbfed565f64139_Family.rowAt F j).val)).length =
      (C10SupplierRowInput.liveList (Packets.live F)).length by
    simp only [Packets.packets,List.length_ofFn]]
  rw [show PCJ38fbfed565f64139_Family.rawBefore a F g j.val ++
      (Packets.packets a F g (PCJ38fbfed565f64139_Family.rowAt F j).val).flatMap
        P1CompactNativeFamily.rawWord ++ PCJ38fbfed565f64139_Family.rawAfter a F g j.val =
      rawFamily a F g from raw_split a F g j]

/-- No row-index branch: a nonempty family's terminal bank retains all words. -/
def headerBank (_j : Nat) : Fin 440 → List Bool :=
  if F.rows = [] then
    fun k => if k=0 then exactListWord (Packets.pool a F g) else []
  else fun k => ZeroPadding.pad (reserve k) (commonHeader a F g layout k)

theorem headerBank_at (j : Fin F.rows.attach.length) :
    headerBank a F g layout reserve j.val = fun k => ZeroPadding.pad (reserve k)
      (PCJcc051fd4c1bd4540_Header.input a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val []
        (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
        (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) k) := by
  have hn : F.rows ≠ [] := by
    intro he
    have hj : j.val < F.rows.length := by simpa only [List.length_attach] using j.isLt
    have hlen : F.rows.length = 0 := congrArg List.length he
    omega
  rw [headerBank,if_neg hn,commonHeader_at a F g layout j]

theorem headerBank_successor (j : Nat) :
    headerBank a F g layout reserve (j+1) = headerBank a F g layout reserve j := rfl

/-- The Frame block at row entry: the descriptor holds `out`, every payload port and the
copier counter hold the cleared `copyCap` backing. -/
def frameBank (out : List Bool) (k : Fin (P1TopDownPaidPayload.tapes printer+2)) : List Bool :=
  if k.val=P1TopDownPaidPayload.tapes printer then ZeroPadding.pad caps.descriptorReserve out
  else List.replicate caps.copyCap false

/-- The work block: a retained bank plus the two produced cleanup ports. -/
def workBank (j : Nat) (k : Fin (rowWork work)) : List Bool :=
  if k=drv then List.replicate caps.copyCap true
  else if k=lg then List.replicate (caps.copyCap+1) false else base j k

def bank (j : Nat) (out : List Bool) : Fin (rowTapes printer work) → List Bool :=
  portCases printer work (headerBank a F g layout reserve j) (frameBank printer caps out)
    (workBank work caps base drv lg j)

def headBank (j : Nat) (out : List Bool) : Fin (rowTapes printer work) → Nat :=
  portCases printer work
    (CompactColdFamily.ambientH [] (PCJ38fbfed565f64139_Family.rawBefore a F g j))
    (PCJ38fbfed565f64139_Row.Frame.heads (P1TopDownPaidPayload.tapes printer) out) (fun _=>0)

/-! ## 3. The state -/

/-- **The `Core.state` choice.**  `rowFuel` and the completion fuel stay parameters: they are
the two numbers the completion machine, not the layout, has to pay. -/
def rowState (completeFuel rowFuel : Nat) :
    PCJ38fbfed565f64139_Family.State (t:=rowTapes printer work) printer where
  heads := headBank printer work a F g
  tapes := bank printer work a F g layout caps reserve base drv lg
  headerReserve := fun _=>reserve
  descriptorReserve := fun _=>caps.descriptorReserve
  headerHeads := headBank printer work a F g
  headerTapes := bank printer work a F g layout caps reserve base drv lg
  frameHeads := fun j out=>headBank printer work a F g (j+1) out
  frameTapes := fun j out=>bank printer work a F g layout caps reserve base drv lg (j+1) out
  fieldReserve := fun _ _=>caps.copyCap
  copyCap := fun _=>caps.copyCap
  prepareFuel := fun _=>0
  completeFuel := fun _=>completeFuel
  cleanupFuel := fun _=>2*caps.copyCap+4
  rowFuel := rowFuel

/-! ## 4. The obligations the state alone discharges -/

variable (p : PCJ38fbfed565f64139_Ready.Program printer (rowWork work))

/-- **`b.entryH=Row.headerInH`.**  The entry heads already dock the cold ambient. -/
theorem entry_heads (j : Nat) (out : List Bool) :
    headBank printer work a F g j out=
      dockH (PCJ38fbfed565f64139_Ready.code p).headerSlots (headBank printer work a F g j out)
        (CompactColdFamily.ambientH [] (PCJ38fbfed565f64139_Family.rawBefore a F g j)) :=
  (dockH_existing (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)) _ _
    (fun k=>portCases_header printer work _ _ _ k)).symm

/-- **`b.entryA=Row.headerInA`.**  The entry bank already carries the row's Header input at
its explicit retained reserve; allocation remains owed by initialization. -/
theorem entry_tapes (j : Fin F.rows.attach.length) (out : List Bool) :
    bank printer work a F g layout caps reserve base drv lg j.val out=
      install (PCJ38fbfed565f64139_Ready.code p).headerSlots
        (bank printer work a F g layout caps reserve base drv lg j.val out)
        (fun k=>ZeroPadding.pad (reserve k) (PCJcc051fd4c1bd4540_Header.input a F g layout
          (PCJ38fbfed565f64139_Family.rowAt F j).val []
          (PCJ38fbfed565f64139_Family.rawBefore a F g j.val)
          (PCJ38fbfed565f64139_Family.rawAfter a F g j.val) k)) := by
  refine (install_existing (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work)) _ _
    (fun k=>?_)).symm
  rw [bank,portCases_header,headerBank_at]

/-! ### The descriptor port -/

theorem descriptor_heads (j : Nat) (out : List Bool) :
    headBank printer work a F g j out
      (PCJ38fbfed565f64139_Ready.descriptor printer (rowWork work))=out.length := by
  rw [PCJ38fbfed565f64139_Ready.descriptor,headBank,portCases_frame]
  simp only [PCJeb9c0f0306e9481c_FramingSpec.heads,PCJeb9c0f0306e9481c_FramingSpec.target,
    Fin.addCases_right]
  rfl

theorem descriptor_tapes (j : Nat) (out : List Bool) :
    bank printer work a F g layout caps reserve base drv lg j out
      (PCJ38fbfed565f64139_Ready.descriptor printer (rowWork work))=
      ZeroPadding.pad caps.descriptorReserve out := by
  rw [PCJ38fbfed565f64139_Ready.descriptor,bank,portCases_frame,frameBank,if_pos]
  rfl

/-! ### The Frame block at every other port -/

theorem payload_entry (j : Nat) (out : List Bool)
    (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    bank printer work a F g layout caps reserve base drv lg j out
      (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) (k.castAdd 2))=
      List.replicate caps.copyCap false := by
  rw [bank,portCases_frame,frameBank,if_neg]
  exact Nat.ne_of_lt k.isLt

theorem counter_entry (j : Nat) (out : List Bool) :
    bank printer work a F g layout caps reserve base drv lg j out
      (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
        (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer)))=
      List.replicate caps.copyCap false := by
  rw [bank,portCases_frame,frameBank,if_neg]
  change P1TopDownPaidPayload.tapes printer+1≠P1TopDownPaidPayload.tapes printer
  omega

/-! ### The two cleanup ports -/

theorem driver_entry (j : Nat) (out : List Bool) :
    bank printer work a F g layout caps reserve base drv lg j out (workSlot printer work drv)=
      List.replicate caps.copyCap true := by
  rw [bank,portCases_work,workBank,if_pos rfl]

theorem log_entry (hne : drv≠lg) (j : Nat) (out : List Bool) :
    bank printer work a F g layout caps reserve base drv lg j out (workSlot printer work lg)=
      List.replicate (caps.copyCap+1) false := by
  rw [bank,portCases_work,workBank,if_neg (Ne.symm hne),if_pos rfl]

theorem cleanup_heads (j : Nat) (out : List Bool) (k : Fin (rowWork work)) :
    headBank printer work a F g j out (workSlot printer work k)=0 := by
  rw [headBank,portCases_work]

/-! ## 5. The cleanup slot map

`Core.mutableTapes` is the whole payload block, so `Plan.ClearBank`'s `Fin (m+1+1)` is
`Fin (tapes printer + 1 + 1)`: the payload ports, then the TRUE unary cap driver, then the
FALSE log.  The nesting is literally that of `Plan.clearInput`, so its three branches meet
these three port families without any re-indexing. -/

def clearSlots (i : Fin (P1TopDownPaidPayload.tapes printer+1+1)) :
    Fin (rowTapes printer work) :=
  Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1)
    (Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1)
      (fun k=>PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) (k.castAdd 2))
      (fun _ : Fin 1=>workSlot printer work drv))
    (fun _ : Fin 1=>workSlot printer work lg) i

theorem clearSlots_field (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    clearSlots printer work drv lg ((k.castAdd 1).castAdd 1)=
      PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) (k.castAdd 2) := by
  simp only [clearSlots,Fin.addCases_left]

theorem clearSlots_driver (k : Fin 1) :
    clearSlots printer work drv lg ((Fin.natAdd (P1TopDownPaidPayload.tapes printer) k).castAdd 1)=
      workSlot printer work drv := by
  simp only [clearSlots,Fin.addCases_left,Fin.addCases_right]

theorem clearSlots_log (k : Fin 1) :
    clearSlots printer work drv lg (Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) k)=
      workSlot printer work lg := by
  simp only [clearSlots,Fin.addCases_right]

/-! ### Port arithmetic -/

theorem headerSlot_val (k : Fin 440) :
    (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k).val=k.val := rfl

theorem frameSlot_val (k : Fin (P1TopDownPaidPayload.tapes printer+2)) :
    (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k).val=440+k.val := rfl

theorem workSlot_val (k : Fin (rowWork work)) :
    (workSlot printer work k).val=440+(P1TopDownPaidPayload.tapes printer+2)+k.val := rfl

theorem header_ne_frame (k : Fin 440) (m : Fin (P1TopDownPaidPayload.tapes printer+2)) :
    PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k≠
      PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) m := by
  intro he
  have hv := congrArg Fin.val he
  rw [headerSlot_val,frameSlot_val] at hv
  have := k.isLt
  omega

theorem header_ne_work (k : Fin 440) (m : Fin (rowWork work)) :
    PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k≠workSlot printer work m := by
  intro he
  have hv := congrArg Fin.val he
  rw [headerSlot_val,workSlot_val] at hv
  have := k.isLt
  omega

theorem frame_ne_work (k : Fin (P1TopDownPaidPayload.tapes printer+2))
    (m : Fin (rowWork work)) :
    PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k≠workSlot printer work m := by
  intro he
  have hv := congrArg Fin.val he
  rw [frameSlot_val,workSlot_val] at hv
  have := k.isLt
  omega

/-- Every row port is a Header port, a Frame port or a work port. -/
theorem port_classify (i : Fin (rowTapes printer work)) :
    (∃ k,i=PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k) ∨
      (∃ k,i=PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k) ∨
      (∃ k,i=workSlot printer work k) := by
  refine Fin.addCases (m:=440+(P1TopDownPaidPayload.tapes printer+2)) (n:=rowWork work)
    (fun k=>?_) (fun k=>Or.inr (Or.inr ⟨k,rfl⟩)) i
  exact Fin.addCases (m:=440) (n:=P1TopDownPaidPayload.tapes printer+2)
    (fun k2=>Or.inl ⟨k2,rfl⟩) (fun k2=>Or.inr (Or.inl ⟨k2,rfl⟩)) k

/-! ### `Core.injective` -/

theorem clear_val (i : Fin (P1TopDownPaidPayload.tapes printer+1+1)) :
    (clearSlots printer work drv lg i).val=
      if i.val<P1TopDownPaidPayload.tapes printer then 440+i.val
      else if i.val=P1TopDownPaidPayload.tapes printer then
        440+(P1TopDownPaidPayload.tapes printer+2)+drv.val
      else 440+(P1TopDownPaidPayload.tapes printer+2)+lg.val := by
  refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1) (fun k=>?_) (fun k=>?_) i
  · refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1) (fun k2=>?_) (fun k2=>?_) k
    · have hv : (((k2.castAdd 1).castAdd 1 :
          Fin (P1TopDownPaidPayload.tapes printer+1+1))).val=k2.val := rfl
      rw [clearSlots_field,hv,if_pos k2.isLt,frameSlot_val]
      rfl
    · have hk : k2.val=0 := Nat.lt_one_iff.mp k2.isLt
      have hv : ((((Fin.natAdd (P1TopDownPaidPayload.tapes printer) k2).castAdd 1) :
          Fin (P1TopDownPaidPayload.tapes printer+1+1))).val=
          P1TopDownPaidPayload.tapes printer := by
        change P1TopDownPaidPayload.tapes printer+k2.val=_
        omega
      rw [clearSlots_driver,hv,if_neg (Nat.lt_irrefl _),if_pos rfl,workSlot_val]
  · have hk : k.val=0 := Nat.lt_one_iff.mp k.isLt
    have hv : (((Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) k) :
        Fin (P1TopDownPaidPayload.tapes printer+1+1))).val=
        P1TopDownPaidPayload.tapes printer+1 := by
      change P1TopDownPaidPayload.tapes printer+1+k.val=_
      omega
    rw [clearSlots_log,hv,if_neg (by omega),if_neg (by omega),workSlot_val]

/-- **`Core.injective`.** -/
theorem clear_injective (hne : drv≠lg) :
    Function.Injective (clearSlots printer work drv lg) := by
  have hdl : drv.val≠lg.val := fun he=>hne (Fin.ext he)
  intro i j h
  have hv := congrArg Fin.val h
  rw [clear_val,clear_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  have hd := drv.isLt
  have hl := lg.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ## 6. Two whole `Core` fields -/

end
end PCJ45bee56da9f34d5a_RowState

