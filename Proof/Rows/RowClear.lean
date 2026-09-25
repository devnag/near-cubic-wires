import Proof.Rows.RowState

/-!
# The cleanup certificate of one row

`Plan.ClearBank` is a bank equality certificate, not an assumed execution: it asks for a cap,
a log capacity, the logical words being erased, the reserve of each cleared port, and the two
bank equations relating the Framing stage's exit to the next row's entry.

Every one of those is fixed by the `state` of `PCJ45bee56da9f34d5a_RowState`:

* `cap := caps.copyCap` and `logCapacity := caps.copyCap+1`, so `logFits` is `le_refl`;
* `logical k` is the framed payload word `frame (Frame.fields printer d k)`, whose length is
  `2*(Frame.fields printer d k).length+1`, i.e. exactly what `RowCaps.Good` caps;
* the cleared ports are the whole payload block plus the TRUE unary driver at `drv` and the
  FALSE log at `lg`; the descriptor target and the copier counter are NOT swept, so
  `rowBudget` never charges `descriptorReserve`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowClear
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

variable (printer : WilliamsAlgorithm) (work : Nat)

/-! ## 1. Frame-bank projections -/

theorem pad_self (n : Nat) (b : Bool) :
    ZeroPadding.pad n (List.replicate n b)=List.replicate n b := by
  simp [ZeroPadding.pad]

theorem target_val :
    (PCJeb9c0f0306e9481c_FramingSpec.target (P1TopDownPaidPayload.tapes printer)).val=
      P1TopDownPaidPayload.tapes printer := rfl

theorem counter_val :
    (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer)).val=
      P1TopDownPaidPayload.tapes printer+1 := rfl

theorem reserve_field (R : Nat) (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    PCJ38fbfed565f64139_Row.Frame.targetReserve (P1TopDownPaidPayload.tapes printer) R
      (k.castAdd 2)=0 := by
  rw [PCJ38fbfed565f64139_Row.Frame.targetReserve,if_neg]
  exact Nat.ne_of_lt k.isLt

theorem reserve_target (R : Nat) :
    PCJ38fbfed565f64139_Row.Frame.targetReserve (P1TopDownPaidPayload.tapes printer) R
      (PCJeb9c0f0306e9481c_FramingSpec.target (P1TopDownPaidPayload.tapes printer))=R := by
  rw [PCJ38fbfed565f64139_Row.Frame.targetReserve,if_pos (target_val printer)]

theorem reserve_counter (R : Nat) :
    PCJ38fbfed565f64139_Row.Frame.targetReserve (P1TopDownPaidPayload.tapes printer) R
      (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer))=0 := by
  rw [PCJ38fbfed565f64139_Row.Frame.targetReserve,if_neg]
  rw [counter_val]
  omega

variable (Fr : Fin (P1TopDownPaidPayload.tapes printer) → Nat)
  (A : Fin (P1TopDownPaidPayload.tapes printer) → List Bool) (o : List Bool) (cap : Nat)

theorem paddedBank_field (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    PCJ38fbfed565f64139_Row.Frame.bank Fr A o cap (k.castAdd 2)=
      ZeroPadding.pad (Fr k) (frame (A k)) := by
  simp only [PCJeb9c0f0306e9481c_FramingSpec.paddedBank,Fin.addCases_left]

theorem paddedBank_target :
    PCJ38fbfed565f64139_Row.Frame.bank Fr A o cap
      (PCJeb9c0f0306e9481c_FramingSpec.target (P1TopDownPaidPayload.tapes printer))=o := by
  simp only [PCJeb9c0f0306e9481c_FramingSpec.paddedBank,
    PCJeb9c0f0306e9481c_FramingSpec.target,Fin.addCases_right]
  rfl

theorem paddedBank_counter :
    PCJ38fbfed565f64139_Row.Frame.bank Fr A o cap
      (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer))=
      List.replicate cap false := by
  simp only [PCJeb9c0f0306e9481c_FramingSpec.paddedBank,
    PCJeb9c0f0306e9481c_FramingSpec.counter,Fin.addCases_right]
  rfl

theorem frameHeads_field (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    PCJ38fbfed565f64139_Row.Frame.heads (P1TopDownPaidPayload.tapes printer) o
      (k.castAdd 2)=0 := by
  simp only [PCJeb9c0f0306e9481c_FramingSpec.heads,Fin.addCases_left]

/-! ## 2. The cleared-bank projections of `Plan.clearInput` / `Plan.clearOutput` -/

variable (K L : Nat) (W : Fin (P1TopDownPaidPayload.tapes printer) → List Bool)

theorem clearInput_field (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    PCJ45bee56da9f34d5a_Plan.clearInput K L W ((k.castAdd 1).castAdd 1)=W k := by
  simp only [PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_left]

theorem clearInput_driver (k : Fin 1) :
    PCJ45bee56da9f34d5a_Plan.clearInput K L W
      ((Fin.natAdd (P1TopDownPaidPayload.tapes printer) k).castAdd 1)=
      List.replicate K true := by
  simp only [PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_left,Fin.addCases_right]

theorem clearInput_log (k : Fin 1) :
    PCJ45bee56da9f34d5a_Plan.clearInput K L W
      (Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) k)=List.replicate L false := by
  simp only [PCJ45bee56da9f34d5a_Plan.clearInput,Fin.addCases_right]

/-- The reserve of each cleared port: `copyCap` on the payload block and on the driver,
`copyCap+1` on the log. -/
def clearReserve (caps : RowCaps) : Fin (P1TopDownPaidPayload.tapes printer+1+1) → Nat :=
  Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1)
    (Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1)
      (fun _=>caps.copyCap) (fun _ : Fin 1=>caps.copyCap))
    (fun _ : Fin 1=>caps.copyCap+1)

variable (caps : RowCaps)

theorem clearReserve_field (k : Fin (P1TopDownPaidPayload.tapes printer)) :
    clearReserve printer caps ((k.castAdd 1).castAdd 1)=caps.copyCap := by
  simp only [clearReserve,Fin.addCases_left]

theorem clearReserve_driver (k : Fin 1) :
    clearReserve printer caps ((Fin.natAdd (P1TopDownPaidPayload.tapes printer) k).castAdd 1)=
      caps.copyCap := by
  simp only [clearReserve,Fin.addCases_left,Fin.addCases_right]

theorem clearReserve_log (k : Fin 1) :
    clearReserve printer caps (Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) k)=
      caps.copyCap+1 := by
  simp only [clearReserve,Fin.addCases_right]

/-! ## 3. The cleanup slots miss every retained port -/

variable (drv lg : Fin (rowWork work))

theorem clear_ne_header (m : Fin (P1TopDownPaidPayload.tapes printer+1+1)) (k : Fin 440) :
    clearSlots printer work drv lg m≠
      PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork work) k := by
  intro he
  have hv := congrArg Fin.val he
  rw [clear_val,headerSlot_val] at hv
  have := k.isLt
  split_ifs at hv <;> omega

theorem clear_ne_target (m : Fin (P1TopDownPaidPayload.tapes printer+1+1)) :
    clearSlots printer work drv lg m≠
      PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
        (PCJeb9c0f0306e9481c_FramingSpec.target (P1TopDownPaidPayload.tapes printer)) := by
  intro he
  have hv := congrArg Fin.val he
  rw [clear_val,frameSlot_val,target_val] at hv
  have hm := m.isLt
  split_ifs at hv <;> omega

theorem clear_ne_counter (m : Fin (P1TopDownPaidPayload.tapes printer+1+1)) :
    clearSlots printer work drv lg m≠
      PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
        (PCJeb9c0f0306e9481c_FramingSpec.counter (P1TopDownPaidPayload.tapes printer)) := by
  intro he
  have hv := congrArg Fin.val he
  rw [clear_val,frameSlot_val,counter_val] at hv
  have hm := m.isLt
  split_ifs at hv <;> omega

theorem clear_ne_work (m : Fin (P1TopDownPaidPayload.tapes printer+1+1))
    (k : Fin (rowWork work)) (hd : k≠drv) (hl : k≠lg) :
    clearSlots printer work drv lg m≠workSlot printer work k := by
  have hdv : drv.val≠k.val := fun he=>hd (Fin.ext he).symm
  have hlv : lg.val≠k.val := fun he=>hl (Fin.ext he).symm
  intro he
  have hv := congrArg Fin.val he
  rw [clear_val,workSlot_val] at hv
  have hm := m.isLt
  split_ifs at hv <;> omega

/-! ## 4. The certificate -/

variable {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (reserve : Fin 440 → Nat) (baseBank : Nat → Fin (rowWork work) → List Bool)
  (row : Packets.Row F.occurrences Lq) (hr : row ∈ F.rows)
  (fact : Packets.PacketFacts a F g row)
  (c : PCJ38fbfed565f64139_Row.Code printer (rowTapes printer work))
  (b : PCJ38fbfed565f64139_Row.Banks printer (rowTapes printer work))
  (j : Nat) (out : List Bool)

/-- **`Core.completeReady`'s cleanup witness.**  Every field is read off the chosen `state`;
nothing about the completion machine is used. -/
def clearBank
    (hfs : c.frameSlots=PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work))
    (hfh : b.frameH=headBank printer work a F g (j+1) out)
    (hfa : b.frameA=bank printer work a F g layout caps reserve baseBank drv lg (j+1) out)
    (hdr : b.descriptorReserve=caps.descriptorReserve)
    (hfr : b.fieldReserve=fun _=>caps.copyCap)
    (hcc : b.copyCap=caps.copyCap)
    (hxh : b.exitH=headBank printer work a F g (j+1)
      (out++(Packets.datum a F g layout row hr fact).word printer))
    (hxa : b.exitA=bank printer work a F g layout caps reserve baseBank drv lg (j+1)
      (out++(Packets.datum a F g layout row hr fact).word printer))
    (hne : drv≠lg)
    (hcap : ∀ i,2*(PCJ38fbfed565f64139_Row.Frame.fields printer
      (Packets.datum a F g layout row hr fact) i).length+1≤caps.copyCap) :
    PCJ45bee56da9f34d5a_Plan.ClearBank (clearSlots printer work drv lg)
      (PCJ38fbfed565f64139_Row.frameOutH printer c a F g layout row hr fact b out) b.exitH
      (PCJ38fbfed565f64139_Row.frameOutA printer c a F g layout row hr fact b out) b.exitA where
  cap := caps.copyCap
  logCapacity := caps.copyCap+1
  logical := fun k=>frame (PCJ38fbfed565f64139_Row.Frame.fields printer
    (Packets.datum a F g layout row hr fact) k)
  reserve := clearReserve printer caps
  fits := by
    intro k
    rw [frame_length]
    exact hcap k
  logFits := Nat.le_refl _
  heads := by
    intro i
    refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1) (fun k=>?_) (fun k=>?_) i
    · refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1)
        (fun k2=>?_) (fun k2=>?_) k
      · rw [clearSlots_field,PCJ38fbfed565f64139_Row.frameOutH,hfs,
          dockH_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer (rowWork work))]
        exact frameHeads_field printer _ k2
      · rw [clearSlots_driver,PCJ38fbfed565f64139_Row.frameOutH,hfs,
          dockH_other _ _ _ _ (fun m=>frame_ne_work printer work m drv),hfh]
        exact cleanup_heads printer work a F g (j+1) out drv
    · rw [clearSlots_log,PCJ38fbfed565f64139_Row.frameOutH,hfs,
        dockH_other _ _ _ _ (fun m=>frame_ne_work printer work m lg),hfh]
      exact cleanup_heads printer work a F g (j+1) out lg
  input := by
    intro i
    refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1) (fun k=>?_) (fun k=>?_) i
    · refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1)
        (fun k2=>?_) (fun k2=>?_) k
      · rw [clearSlots_field,PCJ38fbfed565f64139_Row.frameOutA,hfs,
          install_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer (rowWork work)),
          reserve_field,ZeroPadding.pad_zero,paddedBank_field,hfr,
          clearReserve_field,clearInput_field]
      · rw [clearSlots_driver,PCJ38fbfed565f64139_Row.frameOutA,hfs,
          install_other _ _ _ _ (fun m=>frame_ne_work printer work m drv),hfa,
          driver_entry,clearReserve_driver,clearInput_driver,pad_self]
    · rw [clearSlots_log,PCJ38fbfed565f64139_Row.frameOutA,hfs,
        install_other _ _ _ _ (fun m=>frame_ne_work printer work m lg),hfa,
        log_entry _ _ _ _ _ _ _ _ _ _ _ hne,clearReserve_log,clearInput_log,pad_self]
  finalHeads := by
    rw [hxh]
    funext i
    rcases port_classify printer work i with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
    · rw [headBank,portCases_header,PCJ38fbfed565f64139_Row.frameOutH,hfs,
        dockH_other _ _ _ _ (fun m=>(header_ne_frame printer work k m).symm),hfh,
        headBank,portCases_header]
    · rw [headBank,portCases_frame,PCJ38fbfed565f64139_Row.frameOutH,hfs,
        dockH_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer (rowWork work))]
    · rw [headBank,portCases_work,PCJ38fbfed565f64139_Row.frameOutH,hfs,
        dockH_other _ _ _ _ (fun m=>frame_ne_work printer work m k),hfh,
        headBank,portCases_work]
  finalTapes := by
    rw [hxa]
    funext i
    rcases port_classify printer work i with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
    · rw [install_other _ _ _ _ (fun m=>clear_ne_header printer work drv lg m k),
        PCJ38fbfed565f64139_Row.frameOutA,hfs,
        install_other _ _ _ _ (fun m=>(header_ne_frame printer work k m).symm),hfa,
        bank,portCases_header,bank,portCases_header]
    · refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer+1) (n:=1)
        (fun k2=>?_) (fun k2=>?_) k
      · refine Fin.addCases (m:=P1TopDownPaidPayload.tapes printer) (n:=1)
          (fun k3=>?_) (fun k3=>?_) k2
        · rw [show PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
              (Fin.castAdd 1 (Fin.castAdd 1 k3))=
              clearSlots printer work drv lg ((k3.castAdd 1).castAdd 1) from
            (clearSlots_field printer work drv lg k3).symm,
            install_slot _ (clear_injective printer work drv lg hne),
            clearReserve_field,PCJ45bee56da9f34d5a_Plan.clearOutput,clearInput_field,pad_self,
            clearSlots_field,bank,portCases_frame,frameBank]
          rw [if_neg]
          exact Nat.ne_of_lt k3.isLt
        · have h1 : k3=0 := Subsingleton.elim k3 0
          subst h1
          rw [show PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
              (Fin.castAdd 1 (Fin.natAdd (P1TopDownPaidPayload.tapes printer) (0 : Fin 1)))=
              PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
                (PCJeb9c0f0306e9481c_FramingSpec.target
                  (P1TopDownPaidPayload.tapes printer)) from rfl,
            install_other _ _ _ _ (fun m=>clear_ne_target printer work drv lg m),
            PCJ38fbfed565f64139_Row.frameOutA,hfs,
            install_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer (rowWork work)),
            reserve_target,paddedBank_target,hdr,bank,portCases_frame,frameBank,
            if_pos (target_val printer)]
      · have h1 : k2=0 := Subsingleton.elim k2 0
        subst h1
        rw [show PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
            (Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) (0 : Fin 1))=
            PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork work)
              (PCJeb9c0f0306e9481c_FramingSpec.counter
                (P1TopDownPaidPayload.tapes printer)) from rfl,
          install_other _ _ _ _ (fun m=>clear_ne_counter printer work drv lg m),
          PCJ38fbfed565f64139_Row.frameOutA,hfs,
          install_slot _ (PCJ38fbfed565f64139_Ready.frame_injective printer (rowWork work)),
          reserve_counter,ZeroPadding.pad_zero,paddedBank_counter,hcc,bank,portCases_frame,
          frameBank,if_neg]
        rw [counter_val]
        omega
    · by_cases hd : k=drv
      · rw [hd,show workSlot printer work drv=
            clearSlots printer work drv lg
              ((Fin.natAdd (P1TopDownPaidPayload.tapes printer) (0 : Fin 1)).castAdd 1) from
          (clearSlots_driver printer work drv lg 0).symm,
          install_slot _ (clear_injective printer work drv lg hne),
          clearReserve_driver,PCJ45bee56da9f34d5a_Plan.clearOutput,clearInput_driver,pad_self,
          clearSlots_driver,driver_entry]
      · by_cases hl : k=lg
        · rw [hl,show workSlot printer work lg=
              clearSlots printer work drv lg
                (Fin.natAdd (P1TopDownPaidPayload.tapes printer+1) (0 : Fin 1)) from
            (clearSlots_log printer work drv lg 0).symm,
            install_slot _ (clear_injective printer work drv lg hne),
            clearReserve_log,PCJ45bee56da9f34d5a_Plan.clearOutput,clearInput_log,pad_self,
            clearSlots_log,log_entry _ _ _ _ _ _ _ _ _ _ _ hne]
        · rw [install_other _ _ _ _ (fun m=>clear_ne_work printer work drv lg m k hd hl),
            PCJ38fbfed565f64139_Row.frameOutA,hfs,
            install_other _ _ _ _ (fun m=>frame_ne_work printer work m k),hfa,
            bank,portCases_work,bank,portCases_work]

end
end PCJ45bee56da9f34d5a_RowClear
