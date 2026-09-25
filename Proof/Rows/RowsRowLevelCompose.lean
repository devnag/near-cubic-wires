import Proof.Rows.RowsRowLevelFrame
import Proof.Rows.RowsRowLevelConstants

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes CompetitorCrossScheduler.producer
noncomputable section

/-- The eight work ports the row-level stages use (program constants). -/
structure RowPorts (work : Nat) where
  drv : Fin (rowWork work)
  lg : Fin (rowWork work)
  tpl : Fin (rowWork work)
  tick : Fin (rowWork work)
  cp : Fin (rowWork work)
  ctr : Fin (rowWork work)
  drvH : Fin (rowWork work)
  lgH : Fin (rowWork work)
  nodup : [drv,lg,tpl,tick,cp,ctr,drvH,lgH].Nodup

variable (printer : WilliamsAlgorithm) (work : Nat) (ps : RowPorts work)

/-- C1's port assignment on the row bank. -/
def c1Ports : Fin 9 → Fin (rowTapes printer work) :=
  ![PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 180,
    PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.drv,
    PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.lg,
    PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.tpl,
    payloadSlot printer (rowWork work) (prepPort printer 1),
    payloadSlot printer (rowWork work) (prepPort printer 2),
    PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.tick,
    fieldSlot printer (rowWork work) 2,
    payloadSlot printer (rowWork work) (prepPort printer 3)]

/-- C2's driver ports on the row bank: Header 53, 3, 141 and the resident `1^C`. -/
def c2Src : Fin 4 → Fin (rowTapes printer work) :=
  ![PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 53,
    PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 3,
    PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 141,
    PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.cp]

/-- The ONE fixed row-level machine: C1 ; C2 ; C4. -/
def rowLevelMachine :=
  Composition.machine (streamMachine (c1Ports printer work ps))
    (Composition.machine
      (RecoveryFocus.machine (constSlots (c2Src printer work ps) (fieldSlot printer (rowWork work) ∘ constIdx)
        (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.ctr)) PCJ45bee56da9f34d5a_Constants.machine)
      (PCJ45bee56da9f34d5a_HeaderRewind.headerClear printer work ps.drvH ps.lgH))

/-! ## 1. Port arithmetic -/

theorem workSlot_val' (k : Fin (rowWork work)) :
    (PCJ45bee56da9f34d5a_RowState.workSlot printer work k).val=
      440+(P1TopDownPaidPayload.tapes printer+2)+k.val := rfl

theorem c1Ports_val (i : Fin 9) :
    (c1Ports printer work ps i).val=
      (![180,440+(P1TopDownPaidPayload.tapes printer+2)+ps.drv.val,
        440+(P1TopDownPaidPayload.tapes printer+2)+ps.lg.val,
        440+(P1TopDownPaidPayload.tapes printer+2)+ps.tpl.val,441,442,
        440+(P1TopDownPaidPayload.tapes printer+2)+ps.tick.val,492,443] : Fin 9 → Nat) i := by
  fin_cases i <;> rfl

theorem ports_ne (ps : RowPorts work) :
    ps.drv.val≠ps.lg.val ∧ ps.drv.val≠ps.tpl.val ∧ ps.drv.val≠ps.tick.val ∧ ps.drv.val≠ps.cp.val ∧
    ps.drv.val≠ps.ctr.val ∧ ps.drv.val≠ps.drvH.val ∧ ps.drv.val≠ps.lgH.val ∧
    ps.lg.val≠ps.tpl.val ∧ ps.lg.val≠ps.tick.val ∧ ps.lg.val≠ps.cp.val ∧ ps.lg.val≠ps.ctr.val ∧
    ps.lg.val≠ps.drvH.val ∧ ps.lg.val≠ps.lgH.val ∧
    ps.tpl.val≠ps.tick.val ∧ ps.tpl.val≠ps.cp.val ∧ ps.tpl.val≠ps.ctr.val ∧ ps.tpl.val≠ps.drvH.val ∧
    ps.tpl.val≠ps.lgH.val ∧
    ps.tick.val≠ps.cp.val ∧ ps.tick.val≠ps.ctr.val ∧ ps.tick.val≠ps.drvH.val ∧ ps.tick.val≠ps.lgH.val ∧
    ps.cp.val≠ps.ctr.val ∧ ps.cp.val≠ps.drvH.val ∧ ps.cp.val≠ps.lgH.val ∧
    ps.ctr.val≠ps.drvH.val ∧ ps.ctr.val≠ps.lgH.val ∧ ps.drvH.val≠ps.lgH.val := by
  have h := ps.nodup
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨⟨a1,a2,a3,a4,a5,a6,a7⟩,⟨b1,b2,b3,b4,b5,b6⟩,⟨c1,c2,c3,c4,c5⟩,⟨d1,d2,d3,d4⟩,⟨e1,e2,e3⟩,
    ⟨f1,f2⟩,g1,_,_⟩ := h
  exact ⟨fun h=>a1 (Fin.ext h),fun h=>a2 (Fin.ext h),fun h=>a3 (Fin.ext h),fun h=>a4 (Fin.ext h),
    fun h=>a5 (Fin.ext h),fun h=>a6 (Fin.ext h),fun h=>a7 (Fin.ext h),
    fun h=>b1 (Fin.ext h),fun h=>b2 (Fin.ext h),fun h=>b3 (Fin.ext h),fun h=>b4 (Fin.ext h),
    fun h=>b5 (Fin.ext h),fun h=>b6 (Fin.ext h),
    fun h=>c1 (Fin.ext h),fun h=>c2 (Fin.ext h),fun h=>c3 (Fin.ext h),fun h=>c4 (Fin.ext h),
    fun h=>c5 (Fin.ext h),
    fun h=>d1 (Fin.ext h),fun h=>d2 (Fin.ext h),fun h=>d3 (Fin.ext h),fun h=>d4 (Fin.ext h),
    fun h=>e1 (Fin.ext h),fun h=>e2 (Fin.ext h),fun h=>e3 (Fin.ext h),
    fun h=>f1 (Fin.ext h),fun h=>f2 (Fin.ext h),fun h=>g1 (Fin.ext h)⟩

theorem payload_tapes_ge : 80 ≤ P1TopDownPaidPayload.tapes printer := by
  unfold P1TopDownPaidPayload.tapes Paid.tapes WarmPrepare.tapes Reuse.tapes WholePrefix.tapes
  omega

theorem c1_inj0 (j : Fin 9) (h : c1Ports printer work ps 0=c1Ports printer work ps j) : (0 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj1 (j : Fin 9) (h : c1Ports printer work ps 1=c1Ports printer work ps j) : (1 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj2 (j : Fin 9) (h : c1Ports printer work ps 2=c1Ports printer work ps j) : (2 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj3 (j : Fin 9) (h : c1Ports printer work ps 3=c1Ports printer work ps j) : (3 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj4 (j : Fin 9) (h : c1Ports printer work ps 4=c1Ports printer work ps j) : (4 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj5 (j : Fin 9) (h : c1Ports printer work ps 5=c1Ports printer work ps j) : (5 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj6 (j : Fin 9) (h : c1Ports printer work ps 6=c1Ports printer work ps j) : (6 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj7 (j : Fin 9) (h : c1Ports printer work ps 7=c1Ports printer work ps j) : (7 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1_inj8 (j : Fin 9) (h : c1Ports printer work ps 8=c1Ports printer work ps j) : (8 : Fin 9)=j := by
  have hv := congrArg Fin.val h
  rw [c1Ports_val,c1Ports_val] at hv
  obtain ⟨h12,h13,h16,-,-,-,-,h23,h26,-,-,-,-,h36,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  fin_cases j <;> simp at hv ⊢ <;> omega

theorem c1Ports_injective : Function.Injective (c1Ports printer work ps) := by
  intro i j h
  fin_cases i
  · exact c1_inj0 printer work ps j h
  · exact c1_inj1 printer work ps j h
  · exact c1_inj2 printer work ps j h
  · exact c1_inj3 printer work ps j h
  · exact c1_inj4 printer work ps j h
  · exact c1_inj5 printer work ps j h
  · exact c1_inj6 printer work ps j h
  · exact c1_inj7 printer work ps j h
  · exact c1_inj8 printer work ps j h

theorem constSlots_injective' {T : Nat} (src : Fin 4 → Fin T) (outp : Fin 11 → Fin T) (ctr : Fin T)
    (hs : Function.Injective src) (ho : Function.Injective outp) (hso : ∀ a b,src a≠outp b)
    (hsc : ∀ a,src a≠ctr) (hoc : ∀ b,outp b≠ctr) : Function.Injective (constSlots src outp ctr) := by
  intro i j h
  revert h
  refine Fin.addCases (m:=15) (n:=1) (fun i=>?_) (fun e=>?_) i <;>
    refine Fin.addCases (m:=15) (n:=1) (fun j=>?_) (fun f=>?_) j
  · revert i j
    intro i j
    refine Fin.addCases (m:=4) (n:=11) (fun a=>?_) (fun b=>?_) i <;>
      refine Fin.addCases (m:=4) (n:=11) (fun c=>?_) (fun d=>?_) j
    · intro h
      rw [constSlots_src,constSlots_src] at h
      rw [hs h]
    · intro h
      rw [constSlots_src,constSlots_out] at h
      exact absurd h (hso a d)
    · intro h
      rw [constSlots_out,constSlots_src] at h
      exact absurd h.symm (hso c b)
    · intro h
      rw [constSlots_out,constSlots_out] at h
      rw [ho h]
  · intro h
    revert h
    refine Fin.addCases (m:=4) (n:=11) (fun a=>?_) (fun b=>?_) i
    · intro h
      rw [constSlots_src,constSlots_ctr] at h
      exact absurd h (hsc a)
    · intro h
      rw [constSlots_out,constSlots_ctr] at h
      exact absurd h (hoc b)
  · intro h
    revert h
    refine Fin.addCases (m:=4) (n:=11) (fun a=>?_) (fun b=>?_) j
    · intro h
      rw [constSlots_ctr,constSlots_src] at h
      exact absurd h.symm (hsc a)
    · intro h
      rw [constSlots_ctr,constSlots_out] at h
      exact absurd h.symm (hoc b)
  · intro _
    rw [Subsingleton.elim e f]

theorem fieldSlot_val (t : Nat) (k : Fin 13) :
    (fieldSlot printer t k).val=440+(fieldPort printer k).val := rfl

theorem c2Src_val (i : Fin 4) :
    (c2Src printer work ps i).val=
      (![53,3,141,440+(P1TopDownPaidPayload.tapes printer+2)+ps.cp.val] : Fin 4 → Nat) i := by
  fin_cases i <;> rfl

theorem c2_injective : Function.Injective (constSlots (c2Src printer work ps)
    (fieldSlot printer (rowWork work) ∘ constIdx) (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.ctr)) := by
  obtain ⟨-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,hcc,-⟩ := ports_ne work ps
  have ht := payload_tapes_ge printer
  apply constSlots_injective'
  · intro a b h
    have hv := congrArg Fin.val h
    rw [c2Src_val,c2Src_val] at hv
    fin_cases a <;> fin_cases b <;> simp at hv ⊢ <;> omega
  · exact (fieldSlot_injective printer (rowWork work)).comp constIdx_injective
  · intro a b h
    have hv := congrArg Fin.val h
    have hb := (fieldPort printer (constIdx b)).isLt
    simp only [Function.comp_apply,fieldSlot_val] at hv
    rw [c2Src_val] at hv
    fin_cases a <;> simp at hv <;> omega
  · intro a h
    have hv := congrArg Fin.val h
    rw [c2Src_val,workSlot_val'] at hv
    fin_cases a <;> simp at hv <;> omega
  · intro b h
    have hv := congrArg Fin.val h
    have hb := (fieldPort printer (constIdx b)).isLt
    simp only [Function.comp_apply,fieldSlot_val,workSlot_val'] at hv
    omega

/-! ## 2. The entry bank of `complete` at the RowState banks, port class by port class -/

section Entry
variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (caps : RowCaps) (reserve : Fin 440 → Nat)
  (base : Nat → Fin (rowWork work) → List Bool) (j : Fin F.rows.attach.length) (out : List Bool)

/-- `complete`'s entry tapes (`Row.headerOutA` at the RowState banks). -/
abbrev entryA : Fin (rowTapes printer work) → List Bool :=
  install (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work))
    (PCJ45bee56da9f34d5a_RowState.bank printer work a F g layout caps reserve base ps.drv ps.lg j.val out)
    (fun k=>ZeroPadding.pad (reserve k) (hdrTapes a F g layout j k))

/-- `complete`'s entry heads (`Row.headerOutH` at the RowState banks). -/
abbrev entryH : Fin (rowTapes printer work) → Nat :=
  dockH (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work))
    (PCJ45bee56da9f34d5a_RowState.headBank printer work a F g j.val out) (hdrHeads a F g layout j)

theorem entryA_header (k : Fin 440) :
    entryA printer work ps a F g layout caps reserve base j out
      (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=
      ZeroPadding.pad (reserve k) (hdrTapes a F g layout j k) :=
  install_slot _ (PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work)) _ _ k

theorem entryH_header (k : Fin 440) :
    entryH printer work a F g layout j out (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=
      hdrHeads a F g layout j k :=
  dockH_slot _ (PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work)) _ _ k

theorem entryA_work (k : Fin (rowWork work)) :
    entryA printer work ps a F g layout caps reserve base j out (PCJ45bee56da9f34d5a_RowState.workSlot printer work k)=
      PCJ45bee56da9f34d5a_RowState.workBank work caps base ps.drv ps.lg j.val k := by
  rw [entryA,install_other _ _ _ _ (fun i=>PCJ45bee56da9f34d5a_RowState.header_ne_work printer work i k),
    PCJ45bee56da9f34d5a_RowState.bank,PCJ45bee56da9f34d5a_RowState.portCases_work]

theorem entryH_work (k : Fin (rowWork work)) :
    entryH printer work a F g layout j out (PCJ45bee56da9f34d5a_RowState.workSlot printer work k)=0 := by
  rw [entryH,dockH_other _ _ _ _ (fun i=>PCJ45bee56da9f34d5a_RowState.header_ne_work printer work i k),
    PCJ45bee56da9f34d5a_RowState.cleanup_heads]

theorem entryA_payload (i : Fin (P1TopDownPaidPayload.tapes printer)) :
    entryA printer work ps a F g layout caps reserve base j out (payloadSlot printer (rowWork work) i)=
      List.replicate caps.copyCap false := by
  rw [entryA,install_other _ _ _ (payloadSlot printer (rowWork work) i)
    (fun k=>PCJ45bee56da9f34d5a_RowState.header_ne_frame printer work k (i.castAdd 2))]
  exact PCJ45bee56da9f34d5a_RowState.payload_entry printer work a F g layout caps reserve base ps.drv ps.lg _ out i

theorem entryH_payload (i : Fin (P1TopDownPaidPayload.tapes printer)) :
    entryH printer work a F g layout j out (payloadSlot printer (rowWork work) i)=0 := by
  rw [entryH,dockH_other _ _ _ (payloadSlot printer (rowWork work) i)
    (fun k=>PCJ45bee56da9f34d5a_RowState.header_ne_frame printer work k (i.castAdd 2))]
  change PCJ45bee56da9f34d5a_RowState.headBank printer work a F g j.val out
    (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) (i.castAdd 2))=0
  rw [PCJ45bee56da9f34d5a_RowState.headBank,PCJ45bee56da9f34d5a_RowState.portCases_frame]
  simp only [PCJ38fbfed565f64139_Row.Frame.heads,PCJeb9c0f0306e9481c_FramingSpec.heads,Fin.addCases_left]

end Entry

/-! ## 3. C1 ; C2 ; C4 from the exact entry bank -/

def my12 : Fin 12 → Fin 13 := ![0,1,2,3,4,5,6,7,9,10,11,12]

theorem my12_injective : Function.Injective my12 := by decide

section Main
variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (caps : RowCaps) (reserve : Fin 440 → Nat)
  (base : Nat → Fin (rowWork work) → List Bool)
  (facts : ∀ r∈F.rows,Packets.PacketFacts a F g r) (j : Fin F.rows.attach.length) (out : List Bool)

/-- The row's datum. -/
abbrev rowDatum : P1TopDownPaidReusable.Datum :=
  Packets.datum a F g layout (PCJ38fbfed565f64139_Family.rowAt F j).val
    (PCJ38fbfed565f64139_Family.rowAt F j).property (facts _ (PCJ38fbfed565f64139_Family.rowAt F j).property)

/-- The transducer's arity parameter: the pool arity `(s+1)/2+s/2`, `s = residual F`. -/
abbrev rowN : Nat := (Packets.residual F+1)/2+Packets.residual F/2

/-- The bank the row-level step reaches: Header block `headerBank (j+1)`, twelve framed fields,
everything else as at entry. -/
abbrev rowLevelOut : Fin (rowTapes printer work) → List Bool :=
  install (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work))
    (install (fieldSlot printer (rowWork work) ∘ my12)
      (PCJ45bee56da9f34d5a_RowState.bank printer work a F g layout caps reserve base ps.drv ps.lg j.val out)
      (fun k=>ZeroPadding.pad caps.copyCap (frame (fieldWord (rowDatum a F g layout facts j) (my12 k)))))
    (PCJ45bee56da9f34d5a_RowState.headerBank a F g layout reserve (j.val+1))

/-- **The row-level step.** From `complete`'s exact entry bank of row `j` (RowState banks), the one
fixed machine `rowLevelMachine` (C1 ; C2 ; C4) reaches `headBank (j+1) out` and `rowLevelOut`. -/
theorem rowLevel_step (U S1 S2 rT rC : Nat)
    (hcopy : ∀ k,2*(fieldWord (rowDatum a F g layout facts j) k).length+1 ≤ caps.copyCap)
    (hres : ∀ i,reserve (PCJ45bee56da9f34d5a_HeaderErase.mutable i)=U)
    (hU : hdrBudget a F g layout j+1 ≤ U)
    (hS1 : Scan.ticks (rowDatum a F g layout facts j).row ≤ S1)
    (hS2 : PCJ45bee56da9f34d5a_Constants.rawBudget (rowDatum a F g layout facts j).row.p (rowN F)
      (rowDatum a F g layout facts j).Q (rowDatum a F g layout facts j).C ≤ S2)
    (btpl : base j.val ps.tpl=ZeroPadding.pad rT
      (UnaryTemplate.tape (Scan.countFields (rowDatum a F g layout facts j).row)))
    (btick : base j.val ps.tick=List.replicate S1 false)
    (bcp : base j.val ps.cp=ZeroPadding.pad rC (List.replicate layout.C true))
    (bctr : base j.val ps.ctr=List.replicate S2 false)
    (bdrvH : base j.val ps.drvH=List.replicate U true)
    (blgH : base j.val ps.lgH=List.replicate (U+1) false) :
    Step (rowLevelMachine printer work ps)
      ((PCJ45bee56da9f34d5a_HeaderField.budget (rowDatum a F g layout facts j).row caps.copyCap+1+
        (2*caps.copyCap+4))+1+
        ((2*PCJ45bee56da9f34d5a_Constants.rawBudget (rowDatum a F g layout facts j).row.p (rowN F)
          (rowDatum a F g layout facts j).Q (rowDatum a F g layout facts j).C+2)+1+(4*U+9)))
      (entryH printer work a F g layout j out) (entryA printer work ps a F g layout caps reserve base j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer work a F g (j.val+1) out)
      (rowLevelOut printer work ps a F g layout caps reserve base facts j out) := by
  classical
  have hr := (PCJ38fbfed565f64139_Family.rowAt F j).property
  have hf := facts _ hr
  obtain ⟨n12,n13,n16,n14,n15,n17,n18,n23,n26,n24,n25,n27,n28,n36,n34,n35,n37,n38,n64,n65,n67,n68,
    n45,n47,n48,n57,n58,n78⟩ := ports_ne work ps
  have hK := hcopy 2
  have hinj1 := c1Ports_injective printer work ps
  have hH0 : entryH printer work a F g layout j out (c1Ports printer work ps 0)=
      (Header.stream (rowDatum a F g layout facts j).row).length := by
    change entryH printer work a F g layout j out (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 180)=_
    rw [entryH_header]
    exact header180_heads a F g layout _ _ _ hr hf
  have hz : ∀ i,i≠0 → entryH printer work a F g layout j out (c1Ports printer work ps i)=0 := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    · exact entryH_work printer work a F g layout j out ps.drv
    · exact entryH_work printer work a F g layout j out ps.lg
    · exact entryH_work printer work a F g layout j out ps.tpl
    · exact entryH_payload printer work a F g layout j out _
    · exact entryH_payload printer work a F g layout j out _
    · exact entryH_work printer work a F g layout j out ps.tick
    · exact entryH_payload printer work a F g layout j out _
    · exact entryH_payload printer work a F g layout j out _
  -- stage 1: C1
  have st1 := stream_step (c1Ports printer work ps) hinj1
    (rowDatum a F g layout facts j).row caps.copyCap S1 (reserve 180) rT hK hS1
    (entryH printer work a F g layout j out) (entryA printer work ps a F g layout caps reserve base j out)
    hH0 hz
    (by
      change entryA printer work ps a F g layout caps reserve base j out
        (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 180)=_
      rw [entryA_header]
      congr 1
      exact header180_tapes a F g layout _ _ _ hr hf)
    (by
      change entryA printer work ps a F g layout caps reserve base j out
        (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.drv)=_
      rw [entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,if_pos rfl])
    (by
      change entryA printer work ps a F g layout caps reserve base j out
        (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.lg)=_
      rw [entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n12 (congrArg Fin.val h).symm),
        if_pos rfl])
    (by
      change entryA printer work ps a F g layout caps reserve base j out
        (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.tpl)=_
      rw [entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n13 (congrArg Fin.val h).symm),
        if_neg (fun h=>n23 (congrArg Fin.val h).symm),btpl])
    (entryA_payload printer work ps a F g layout caps reserve base j out _)
    (entryA_payload printer work ps a F g layout caps reserve base j out _)
    (by
      change entryA printer work ps a F g layout caps reserve base j out
        (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.tick)=_
      rw [entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n16 (congrArg Fin.val h).symm),
        if_neg (fun h=>n26 (congrArg Fin.val h).symm),btick])
    (entryA_payload printer work ps a F g layout caps reserve base j out _)
    (entryA_payload printer work ps a F g layout caps reserve base j out _)
  -- the heads after stage 1
  have hH1 : ∀ x,dockH (c1Ports printer work ps) (entryH printer work a F g layout j out) (fun _=>0) x=
      if x=c1Ports printer work ps 0 then 0 else entryH printer work a F g layout j out x := by
    intro x
    by_cases hx : ∃ i,c1Ports printer work ps i=x
    · obtain ⟨i,rfl⟩ := hx
      rw [dockH_slot _ hinj1]
      by_cases hi : i=0
      · subst hi
        rw [if_pos rfl]
      · rw [if_neg (fun he=>hi (hinj1 he)),hz i hi]
    · rw [dockH_other _ _ _ _ (fun i he=>hx ⟨i,he⟩),if_neg (fun he=>hx ⟨0,he.symm⟩)]
  -- facts for stage 2
  have ht := payload_tapes_ge printer
  have hW : ∀ k : Fin (rowWork work),∀ i : Fin 13,
      PCJ45bee56da9f34d5a_RowState.workSlot printer work k≠fieldSlot printer (rowWork work) i := by
    intro k i he
    have hv := congrArg Fin.val he
    rw [workSlot_val',fieldSlot_val] at hv
    have := (fieldPort printer i).isLt
    omega
  have hWH : ∀ k : Fin (rowWork work),
      PCJ45bee56da9f34d5a_RowState.workSlot printer work k≠c1Ports printer work ps 0 := by
    intro k he
    have hv := congrArg Fin.val he
    rw [workSlot_val',c1Ports_val] at hv
    simp at hv
    omega
  have hFH : ∀ i : Fin 13,fieldSlot printer (rowWork work) i≠c1Ports printer work ps 0 := by
    intro i he
    have hv := congrArg Fin.val he
    rw [fieldSlot_val,c1Ports_val] at hv
    simp at hv
    omega
  have hs2 : ∀ x : Fin 440,x≠180 →
      PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) x≠c1Ports printer work ps 0 := by
    intro x hx he
    exact hx (PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work) he)
  have hc7 : ∀ i : Fin 11,constIdx i≠2 := by decide
  let A1 : Fin (rowTapes printer work) → List Bool :=
    Function.update (entryA printer work ps a F g layout caps reserve base j out) (c1Ports printer work ps 7)
      (ZeroPadding.pad caps.copyCap (frame (Header.stream (rowDatum a F g layout facts j).row)))
  have hA1 : ∀ x,x≠c1Ports printer work ps 7 →
      A1 x=entryA printer work ps a F g layout caps reserve base j out x :=
    fun x hx=>Function.update_of_ne hx _ _
  -- stage 2: C2
  have st2 := const_row_step printer (rowWork work) (c2Src printer work ps)
    (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.ctr) (c2_injective printer work ps)
    (rowDatum a F g layout facts j) (rowDatum a F g layout facts j).row.p (rowN F)
    (rowDatum a F g layout facts j).Q (rowDatum a F g layout facts j).C
    (by
      change (Packets.residual F+1)/2=((Packets.residual F+1)/2+Packets.residual F/2+1)/2
      omega)
    (by
      change decide (Packets.residual F%2=1)=decide (((Packets.residual F+1)/2+Packets.residual F/2)%2=1)
      have he : ((Packets.residual F+1)/2+Packets.residual F/2)%2=Packets.residual F%2 := by omega
      rw [he])
    rfl rfl rfl ![reserve 53,reserve 3,reserve 141,rC] caps.copyCap S2 hS2
    (dockH (c1Ports printer work ps) (entryH printer work a F g layout j out) (fun _=>0))
    A1
    (by
      intro i
      rw [hH1]
      refine Fin.addCases (m:=15) (n:=1) (fun i=>?_) (fun e=>?_) i
      · refine Fin.addCases (m:=4) (n:=11) (fun k=>?_) (fun m=>?_) i
        · rw [constSlots_src]
          fin_cases k
          · show (if PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 53=
                c1Ports printer work ps 0 then 0 else entryH printer work a F g layout j out
                (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 53))=0
            rw [if_neg (hs2 53 (by decide)),entryH_header]
            exact (header_driver_heads a F g layout _ _ _).1
          · show (if PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 3=
                c1Ports printer work ps 0 then 0 else entryH printer work a F g layout j out
                (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 3))=0
            rw [if_neg (hs2 3 (by decide)),entryH_header]
            exact (header_driver_heads a F g layout _ _ _).2.1
          · show (if PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 141=
                c1Ports printer work ps 0 then 0 else entryH printer work a F g layout j out
                (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 141))=0
            rw [if_neg (hs2 141 (by decide)),entryH_header]
            exact (header_driver_heads a F g layout _ _ _).2.2
          · show (if PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.cp=
                c1Ports printer work ps 0 then 0 else entryH printer work a F g layout j out
                (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.cp))=0
            rw [if_neg (hWH ps.cp)]
            exact entryH_work printer work a F g layout j out ps.cp
        · rw [constSlots_out,Function.comp_apply,if_neg (hFH _)]
          exact entryH_payload printer work a F g layout j out _
      · rw [constSlots_ctr,if_neg (hWH ps.ctr)]
        exact entryH_work printer work a F g layout j out ps.ctr)
    (by
      intro k
      fin_cases k
      · show A1 (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 53)=
          ZeroPadding.pad (reserve 53) (List.replicate (rowDatum a F g layout facts j).row.p true)
        rw [hA1 _ (fun he=>by
          have hv := congrArg Fin.val he
          rw [c1Ports_val] at hv
          change 53=_ at hv
          simp at hv)]
        rw [entryA_header]
        unfold hdrTapes
        rw [header53_tapes a F g layout _ _ _ hr hf]
      · show A1 (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 3)=
          ZeroPadding.pad (reserve 3) (UnaryTemplate.tape (rowN F))
        rw [hA1 _ (fun he=>by
          have hv := congrArg Fin.val he
          rw [c1Ports_val] at hv
          change 3=_ at hv
          simp at hv)]
        rw [entryA_header]
        unfold hdrTapes
        rw [header3_tapes]
      · show A1 (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) 141)=
          ZeroPadding.pad (reserve 141) (false::List.replicate (rowDatum a F g layout facts j).Q true)
        rw [hA1 _ (fun he=>by
          have hv := congrArg Fin.val he
          rw [c1Ports_val] at hv
          change 141=_ at hv
          simp at hv)]
        rw [entryA_header]
        unfold hdrTapes
        rw [header141_tapes]
        rfl
      · show A1 (PCJ45bee56da9f34d5a_RowState.workSlot printer work ps.cp)=
          ZeroPadding.pad rC (List.replicate (rowDatum a F g layout facts j).C true)
        rw [hA1 _ (hW ps.cp 2)]
        rw [entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n14 (congrArg Fin.val h).symm),
          if_neg (fun h=>n24 (congrArg Fin.val h).symm),bcp]
        rfl)
    (by
      intro k
      rw [hA1 _ (fun he=>hc7 k (fieldSlot_injective printer (rowWork work) he))]
      exact entryA_payload printer work ps a F g layout caps reserve base j out _)
    (by
      rw [hA1 _ (hW ps.ctr 2),entryA_work,PCJ45bee56da9f34d5a_RowState.workBank,
        if_neg (fun h=>n15 (congrArg Fin.val h).symm),if_neg (fun h=>n25 (congrArg Fin.val h).symm),bctr])
  -- stage 3: C4
  have hinjF := fieldSlot_injective printer (rowWork work)
  have hinjH := PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work)
  have hFhdr : ∀ (i : Fin 13) (k : Fin 440),
      fieldSlot printer (rowWork work) i≠PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k := by
    intro i k he
    have hv := congrArg Fin.val he
    rw [fieldSlot_val] at hv
    change _=k.val at hv
    have := k.isLt
    omega
  let A2 : Fin (rowTapes printer work) → List Bool :=
    install (fieldSlot printer (rowWork work) ∘ constIdx) A1
      (fun k=>ZeroPadding.pad caps.copyCap (frame (fieldWord (rowDatum a F g layout facts j) (constIdx k))))
  have hA2 : ∀ x,(∀ k,(fieldSlot printer (rowWork work) ∘ constIdx) k≠x) → A2 x=A1 x :=
    fun x hx=>install_other _ _ _ _ hx
  have st3 := header_restore a F g layout j printer work ps.drvH ps.lgH
    (fun h=>n78 (congrArg Fin.val h)) facts reserve U hres hU
    (dockH (c1Ports printer work ps) (entryH printer work a F g layout j out) (fun _=>0)) A2
    (by
      intro k
      rw [hA2 _ (fun i he=>hFhdr _ k he),hA1 _ (fun he=>hFhdr 2 k he.symm),entryA_header])
    (by
      intro i
      rw [hH1]
      split_ifs
      · omega
      · rw [entryH_header]
        have := mutable_head_le a F g layout j facts i
        omega)
    (by
      intro k hk
      have h180 : k≠180 := by
        rintro rfl
        unfold PCJ45bee56da9f34d5a_HeaderErase.retained at hk
        simp at hk
      rw [hH1,if_neg (hs2 k h180),entryH_header])
    (by rw [hH1,if_neg (hWH _),entryH_work])
    (by rw [hH1,if_neg (hWH _),entryH_work])
    (by
      rw [hA2 _ (fun i he=>hW ps.drvH _ he.symm),hA1 _ (hW ps.drvH 2),entryA_work,
        PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n17 (congrArg Fin.val h).symm),
        if_neg (fun h=>n27 (congrArg Fin.val h).symm),bdrvH])
    (by
      rw [hA2 _ (fun i he=>hW ps.lgH _ he.symm),hA1 _ (hW ps.lgH 2),entryA_work,
        PCJ45bee56da9f34d5a_RowState.workBank,if_neg (fun h=>n18 (congrArg Fin.val h).symm),
        if_neg (fun h=>n28 (congrArg Fin.val h).symm),blgH])
  refine (st1.seq (st2.seq st3)).congr ?_ ?_
  · funext x
    by_cases hx : ∃ k,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k=x
    · obtain ⟨k,rfl⟩ := hx
      rw [dockH_slot _ hinjH,PCJ45bee56da9f34d5a_RowState.headBank,
        PCJ45bee56da9f34d5a_RowState.portCases_header]
    · rw [dockH_other _ _ _ _ (fun k he=>hx ⟨k,he⟩),hH1,if_neg (fun he=>hx ⟨180,he.symm⟩),entryH,
        dockH_other _ _ _ _ (fun k he=>hx ⟨k,he⟩)]
      rcases PCJ45bee56da9f34d5a_RowState.port_classify printer work x with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
      · exact absurd ⟨k,rfl⟩ hx
      · rw [PCJ45bee56da9f34d5a_RowState.headBank,PCJ45bee56da9f34d5a_RowState.headBank,
          PCJ45bee56da9f34d5a_RowState.portCases_frame,PCJ45bee56da9f34d5a_RowState.portCases_frame]
      · rw [PCJ45bee56da9f34d5a_RowState.headBank,PCJ45bee56da9f34d5a_RowState.headBank,
          PCJ45bee56da9f34d5a_RowState.portCases_work,PCJ45bee56da9f34d5a_RowState.portCases_work]
  · funext x
    by_cases hx : ∃ k,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k=x
    · obtain ⟨k,rfl⟩ := hx
      rw [install_slot _ hinjH]
      exact (install_slot _ hinjH _ _ k).symm
    · have hn : ∀ k,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k≠x :=
        fun k he=>hx ⟨k,he⟩
      show install _ A2 _ x=install _ _ _ x
      rw [install_other _ _ _ _ hn,install_other _ _ _ _ hn]
      have hinj12 : Function.Injective (fieldSlot printer (rowWork work) ∘ my12) :=
        hinjF.comp my12_injective
      by_cases hm : ∃ m,(fieldSlot printer (rowWork work) ∘ my12) m=x
      · obtain ⟨m,rfl⟩ := hm
        rw [install_slot _ hinj12]
        have hinjc : Function.Injective (fieldSlot printer (rowWork work) ∘ constIdx) :=
          hinjF.comp constIdx_injective
        fin_cases m
        · exact install_slot _ hinjc _ _ 0
        · exact install_slot _ hinjc _ _ 1
        · show A2 (fieldSlot printer (rowWork work) 2)=_
          rw [hA2 _ (fun k he=>hc7 k (hinjF he))]
          exact Function.update_self _ _ _
        · exact install_slot _ hinjc _ _ 2
        · exact install_slot _ hinjc _ _ 3
        · exact install_slot _ hinjc _ _ 4
        · exact install_slot _ hinjc _ _ 5
        · exact install_slot _ hinjc _ _ 6
        · exact install_slot _ hinjc _ _ 7
        · exact install_slot _ hinjc _ _ 8
        · exact install_slot _ hinjc _ _ 9
        · exact install_slot _ hinjc _ _ 10
      · rw [install_other _ _ _ _ (fun m he=>hm ⟨m,he⟩)]
        have hcm : ∀ m : Fin 11,∃ m' : Fin 12,my12 m'=constIdx m := by decide
        rw [hA2 _ (fun k he=>by
          obtain ⟨m',hm'⟩ := hcm k
          exact hm ⟨m',by rw [Function.comp_apply,hm'];exact he⟩),
          hA1 _ (fun he=>hm ⟨2,he.symm⟩),entryA,install_other _ _ _ _ hn]

theorem finish_eq (B : Fin (rowTapes printer work) → List Bool)
    (h8 : B (fieldSlot printer (rowWork work) 8)=
      ZeroPadding.pad caps.copyCap (frame (fieldWord (rowDatum a F g layout facts j) 8)))
    (hwork : ∀ k,B (PCJ45bee56da9f34d5a_RowState.workSlot printer work k)=
      PCJ45bee56da9f34d5a_RowState.workBank work caps base ps.drv ps.lg (j.val+1) k)
    (hrest : ∀ x,x≠fieldSlot printer (rowWork work) 8 →
      (∀ k,PCJ45bee56da9f34d5a_RowState.workSlot printer work k≠x) →
      B x=rowLevelOut printer work ps a F g layout caps reserve base facts j out x) :
    B=install (fieldSlot printer (rowWork work))
      (PCJ45bee56da9f34d5a_RowState.bank printer work a F g layout caps reserve base ps.drv ps.lg (j.val+1) out)
      (fun k=>ZeroPadding.pad caps.copyCap (frame (fieldWord (rowDatum a F g layout facts j) k))) := by
  classical
  have hinjF := fieldSlot_injective printer (rowWork work)
  have hinjH := PCJ38fbfed565f64139_Ready.header_injective printer (rowWork work)
  have hinj12 : Function.Injective (fieldSlot printer (rowWork work) ∘ my12) := hinjF.comp my12_injective
  have ht := payload_tapes_ge printer
  funext x
  rcases PCJ45bee56da9f34d5a_RowState.port_classify printer work x with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · have hFH : ∀ i,fieldSlot printer (rowWork work) i≠PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k := by
      intro i he
      have hv := congrArg Fin.val he
      rw [fieldSlot_val] at hv
      change _=k.val at hv
      have := k.isLt
      omega
    rw [hrest _ (hFH 8).symm (fun m=>PCJ45bee56da9f34d5a_RowState.header_ne_work printer work k m ∘ Eq.symm),
      install_other _ _ _ _ hFH]
    change install _ _ _ (PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k)=_
    rw [install_slot _ hinjH,PCJ45bee56da9f34d5a_RowState.bank,PCJ45bee56da9f34d5a_RowState.portCases_header]
  · have hW : ∀ m,PCJ45bee56da9f34d5a_RowState.workSlot printer work m≠
        PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k :=
      fun m he=>PCJ45bee56da9f34d5a_RowState.frame_ne_work printer work k m he.symm
    by_cases h8x : fieldSlot printer (rowWork work) 8=PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k
    · rw [←h8x,h8,install_slot _ hinjF]
    · rw [hrest _ (fun he=>h8x he.symm) hW]
      change install _ (install (fieldSlot printer (rowWork work) ∘ my12) _ _) _ _=_
      have hFH : ∀ i,PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) i≠
          PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k :=
        fun i=>PCJ45bee56da9f34d5a_RowState.header_ne_frame printer work i k
      rw [install_other _ _ _ _ hFH]
      by_cases hm : ∃ m,(fieldSlot printer (rowWork work) ∘ my12) m=
          PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k
      · obtain ⟨m,hm⟩ := hm
        rw [←hm,install_slot _ hinj12]
        simp only [Function.comp_apply]
        rw [install_slot _ hinjF]
      · rw [install_other _ _ _ _ (fun m he=>hm ⟨m,he⟩)]
        have hn : ∀ i,fieldSlot printer (rowWork work) i≠PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work) k := by
          intro i he
          have hmy : ∀ i : Fin 13,i≠8 → ∃ m,my12 m=i := by decide
          by_cases hi8 : i=8
          · subst hi8
            exact h8x he
          · obtain ⟨m,hm'⟩ := hmy i hi8
            exact hm ⟨m,by rw [Function.comp_apply,hm'];exact he⟩
        rw [install_other _ _ _ _ hn,PCJ45bee56da9f34d5a_RowState.bank,PCJ45bee56da9f34d5a_RowState.bank,
          PCJ45bee56da9f34d5a_RowState.portCases_frame,PCJ45bee56da9f34d5a_RowState.portCases_frame]
  · have hFW : ∀ i,fieldSlot printer (rowWork work) i≠PCJ45bee56da9f34d5a_RowState.workSlot printer work k :=
      fun i he=>PCJ45bee56da9f34d5a_RowState.frame_ne_work printer work _ k he
    rw [hwork,install_other _ _ _ _ hFW,PCJ45bee56da9f34d5a_RowState.bank,
      PCJ45bee56da9f34d5a_RowState.portCases_work]

end Main


end
end RowsRowLevel
