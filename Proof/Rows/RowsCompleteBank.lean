import Proof.Rows.RowsCompleteRow
import Proof.Rows.RowsRowLevelCompose

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CompleteBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.BaseLayout RowsConstruction.MaskStage RowsConstruction.CompleteWork RowsConstruction.CompleteRow
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

section Mach
variable (printer : WilliamsAlgorithm) (NI : Nat)

/-- The work slot of the row bank. -/
abbrev ws (k : Fin (2+rowsWork NI)) : Fin (rowTapes printer (rowsWork NI)) :=
  PCJ45bee56da9f34d5a_RowState.workSlot printer (rowsWork NI) k

/-- C6's ports: the verdict tape, the C6 driver, field 8 (the mask's payload port), the C6 log. -/
def u6 : Fin 4 → Fin (rowTapes printer (rowsWork NI)) :=
  ![ws printer NI (loopPort NI vL), ws printer NI (c6Port NI 0),
    RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8, ws printer NI (c6Port NI 1)]

theorem ws_val (k : Fin (2+rowsWork NI)) :
    (ws printer NI k).val = 440+(P1TopDownPaidPayload.tapes printer+2)+k.val := rfl

theorem ws_injective : Function.Injective (ws printer NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  rw [ws_val, ws_val] at hv
  exact Fin.ext (by omega)

theorem field_ne_ws (k : Fin 13) (m : Fin (2+rowsWork NI)) :
    RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) k ≠ ws printer NI m := by
  intro h
  have hv := congrArg Fin.val h
  rw [RowsRowLevel.fieldSlot_val, ws_val] at hv
  have := (RowsRowLevel.fieldPort printer k).isLt
  omega

theorem u6_injective : Function.Injective (u6 printer NI) := by
  intro x y h
  have hne0 : loopPort NI vL ≠ c6Port NI 0 := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have hne1 : loopPort NI vL ≠ c6Port NI 1 := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this
  have hne2 : c6Port NI 0 ≠ c6Port NI 1 := by
    intro e; have := congrArg Fin.val e; rw [c6Port_val, c6Port_val] at this; simp at this
  have winj := ws_injective printer NI
  fin_cases x <;> fin_cases y <;> simp only [u6] at h ⊢ <;>
    first
    | rfl
    | exact absurd (winj h) hne0
    | exact absurd (winj h) hne1
    | exact absurd (winj h) hne2
    | exact absurd (winj h).symm hne0
    | exact absurd (winj h).symm hne1
    | exact absurd (winj h).symm hne2
    | exact absurd h (field_ne_ws printer NI _ _)
    | exact absurd h.symm (field_ne_ws printer NI _ _)

/-- **`complete`** (one fixed machine). -/
def completeM (ps : RowsRowLevel.RowPorts (rowsWork NI)) (iMode : Fin NI) (ini : Fin 40 → Fin NI)
    (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (iniS : Fin 9 → Fin NI) :=
  Composition.machine (RowsRowLevel.rowLevelMachine printer (rowsWork NI) ps)
    (Composition.machine (RecoveryFocus.machine (ws printer NI) (W1 NI iMode))
      (Composition.machine (RecoveryFocus.machine (u6 printer NI)
          NearCubicWires.RepairSource.ProjectionNormalization.RawFrame.machine)
        (RecoveryFocus.machine (ws printer NI) (W2 NI iMode ini ix ib iOne iniS))))

end Mach

/-! ## The composition for any `base` -/

section Row
variable (printer : WilliamsAlgorithm) (NI : Nat) (ps : RowsRowLevel.RowPorts (rowsWork NI))
  {q Lq : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q Lq)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g) (caps : RowCaps) (reserve : Fin 440 → Nat)
  (base : Nat → Fin (rowWork (rowsWork NI)) → List Bool)
  (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r) (j : Fin F.rows.attach.length) (out : List Bool)

theorem work_eq (hdrv : ∀ i, base i ps.drv = List.replicate caps.copyCap true)
    (hlg : ∀ i, base i ps.lg = List.replicate (caps.copyCap+1) false) (i : Nat) (k : Fin (rowWork (rowsWork NI))) :
    PCJ45bee56da9f34d5a_RowState.workBank (rowsWork NI) caps base ps.drv ps.lg i k = base i k := by
  unfold PCJ45bee56da9f34d5a_RowState.workBank
  split
  · rename_i h; rw [h, hdrv]
  · split
    · rename_i h; rw [h, hlg]
    · rfl

theorem rl_work (hdrv : ∀ i, base i ps.drv = List.replicate caps.copyCap true)
    (hlg : ∀ i, base i ps.lg = List.replicate (caps.copyCap+1) false) (k : Fin (rowWork (rowsWork NI))) :
    RowsRowLevel.rowLevelOut printer (rowsWork NI) ps a F g layout caps reserve base facts j out (ws printer NI k) =
      base j.val k := by
  unfold RowsRowLevel.rowLevelOut
  rw [install_other _ _ _ _ (fun i => PCJ45bee56da9f34d5a_RowState.header_ne_work printer (rowsWork NI) i k),
    install_other _ _ _ _ (fun i => by simp only [Function.comp_apply]; exact field_ne_ws printer NI _ k),
    PCJ45bee56da9f34d5a_RowState.bank, PCJ45bee56da9f34d5a_RowState.portCases_work,
    work_eq NI ps caps base hdrv hlg]

theorem rl_field8 :
    RowsRowLevel.rowLevelOut printer (rowsWork NI) ps a F g layout caps reserve base facts j out
      (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = List.replicate caps.copyCap false := by
  unfold RowsRowLevel.rowLevelOut
  have hx : RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8 =
      PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork (rowsWork NI)) ((RowsRowLevel.fieldPort printer 8).castAdd 2) :=
    rfl
  have hmy : ∀ i : Fin 12, RowsRowLevel.my12 i ≠ 8 := by decide
  rw [hx, install_other _ _ _ _ (fun i => PCJ45bee56da9f34d5a_RowState.header_ne_frame printer (rowsWork NI) i _),
    install_other _ _ _ _ (fun i he => by
      simp only [Function.comp_apply] at he
      rw [← hx] at he
      exact hmy i (RowsRowLevel.fieldSlot_injective printer (rowWork (rowsWork NI)) he))]
  exact PCJ45bee56da9f34d5a_RowState.payload_entry printer (rowsWork NI) a F g layout caps reserve base ps.drv ps.lg
    j.val out _

theorem hb_work (k : Fin (rowWork (rowsWork NI))) :
    PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out (ws printer NI k) = 0 :=
  PCJ45bee56da9f34d5a_RowState.cleanup_heads printer (rowsWork NI) a F g _ out k

theorem hb_field (k : Fin 13) :
    PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out
      (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) k) = 0 := by
  change PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out
    (PCJ38fbfed565f64139_Ready.frameSlots printer (rowWork (rowsWork NI)) ((RowsRowLevel.fieldPort printer k).castAdd 2))=0
  rw [PCJ45bee56da9f34d5a_RowState.headBank, PCJ45bee56da9f34d5a_RowState.portCases_frame]
  simp only [PCJ38fbfed565f64139_Row.Frame.heads, PCJeb9c0f0306e9481c_FramingSpec.heads, Fin.addCases_left]

theorem vne0 (NI : Nat) : loopPort NI vL ≠ c6Port NI 0 := by
  intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this

theorem vne1 (NI : Nat) : loopPort NI vL ≠ c6Port NI 1 := by
  intro e; have := congrArg Fin.val e; rw [c6Port_val, loopPort_val] at this; simp [vL] at this

/-- W1 lifted to the row bank. -/
theorem w1_lift (B0 : Fin (rowWork (rowsWork NI)) → List Bool) (w : List Bool) (iMode : Fin NI) (n1 : Nat)
    (H : Fin (rowTapes printer (rowsWork NI)) → ℕ) (A1 : Fin (rowTapes printer (rowsWork NI)) → List Bool)
    (hbw : ∀ k, H (ws printer NI k) = 0) (rlw : ∀ k, A1 (ws printer NI k) = B0 k)
    (hW1 : Step (W1 NI iMode) n1 (fun _ => 0) B0 (fun _ => 0) (Function.update B0 (loopPort NI vL) w)) :
    Step (RecoveryFocus.machine (ws printer NI) (W1 NI iMode)) n1 H A1 H
      (Function.update A1 (ws printer NI (loopPort NI vL)) w) := by
  have st2 := SymVerdict.focus_at hW1 (ws printer NI) (ws_injective printer NI) H A1 hbw rlw
  rw [dockH_existing _ _ _ hbw, SymVerdict.install_update _ (ws_injective printer NI) A1 _ (loopPort NI vL)
    (fun k hk => by rw [Function.update_of_ne hk, rlw]), Function.update_self] at st2
  exact st2

/-- C6 on the row bank. -/
theorem c6_lift (caps : RowCaps) (B0 : Fin (rowWork (rowsWork NI)) → List Bool) (s : Nat) (w : List Bool)
    (hwl : w.length = 2^s) (hc60 : B0 (c6Port NI 0) = List.replicate (2^s) true)
    (hc61 : B0 (c6Port NI 1) = List.replicate (2*2^s+1) false)
    (H : Fin (rowTapes printer (rowsWork NI)) → ℕ) (A2 : Fin (rowTapes printer (rowsWork NI)) → List Bool)
    (hbw : ∀ k, H (ws printer NI k) = 0) (hbf : H (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = 0)
    (hv : A2 (ws printer NI (loopPort NI vL)) = w)
    (wne : ∀ k, k ≠ loopPort NI vL → A2 (ws printer NI k) = B0 k)
    (a8 : A2 (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = List.replicate caps.copyCap false) :
    Step (RecoveryFocus.machine (u6 printer NI) NearCubicWires.RepairSource.ProjectionNormalization.RawFrame.machine)
      (4*w.length+4) H A2 H
      (Function.update A2 (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8)
        (ZeroPadding.pad caps.copyCap (frame w))) :=
  RowsRowLevel.frame_step (u6 printer NI) (u6_injective printer NI) w caps.copyCap (2*2^s+1) 0 0
    (by omega) H A2
    (fun i => by
      fin_cases i
      · exact hbw _
      · exact hbw _
      · exact hbf
      · exact hbw _)
    (by show A2 (ws printer NI (loopPort NI vL)) = _; rw [hv, ZeroPadding.pad_zero])
    (by show A2 (ws printer NI (c6Port NI 0)) = _
        rw [wne _ (Ne.symm (vne0 NI)), hc60, ZeroPadding.pad_zero, hwl])
    (by show A2 (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = _; exact a8)
    (by show A2 (ws printer NI (c6Port NI 1)) = _; rw [wne _ (Ne.symm (vne1 NI)), hc61])

/-- W2 lifted to the row bank. -/
theorem w2_lift (B0 B1 : Fin (rowWork (rowsWork NI)) → List Bool) (w : List Bool) (iMode : Fin NI)
    (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (iniS : Fin 9 → Fin NI)
    (n2 : Nat) (H : Fin (rowTapes printer (rowsWork NI)) → ℕ) (A3 : Fin (rowTapes printer (rowsWork NI)) → List Bool)
    (hbw : ∀ k, H (ws printer NI k) = 0)
    (a3w : ∀ k, A3 (ws printer NI k) = Function.update B0 (loopPort NI vL) w k)
    (hW2 : Step (W2 NI iMode ini ix ib iOne iniS) n2 (fun _ => 0) (Function.update B0 (loopPort NI vL) w)
      (fun _ => 0) B1) :
    Step (RecoveryFocus.machine (ws printer NI) (W2 NI iMode ini ix ib iOne iniS)) n2 H A3 H
      (install (ws printer NI) A3 B1) := by
  have st4 := SymVerdict.focus_at hW2 (ws printer NI) (ws_injective printer NI) H A3 hbw a3w
  rw [dockH_existing _ _ _ hbw] at st4
  exact st4

/-- The composition with the row-level exit bank, its heads and the target bank abstract. -/
theorem complete_gen (caps : RowCaps) (B0 B1 : Fin (rowWork (rowsWork NI)) → List Bool)
    (iMode : Fin NI) (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI)
    (iniS : Fin 9 → Fin NI) (s : Nat) (w : List Bool) (hwl : w.length = 2^s)
    (hc60 : B0 (c6Port NI 0) = List.replicate (2^s) true)
    (hc61 : B0 (c6Port NI 1) = List.replicate (2*2^s+1) false)
    (c1 n1 n2 : Nat) (H0 H : Fin (rowTapes printer (rowsWork NI)) → ℕ)
    (A0 A1 Tgt : Fin (rowTapes printer (rowsWork NI)) → List Bool)
    (hbw : ∀ k, H (ws printer NI k) = 0)
    (hbf : H (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = 0)
    (rlw : ∀ k, A1 (ws printer NI k) = B0 k)
    (rl8 : A1 (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = List.replicate caps.copyCap false)
    (hfin : ∀ B : Fin (rowTapes printer (rowsWork NI)) → List Bool,
      B (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) = ZeroPadding.pad caps.copyCap (frame w) →
      (∀ k, B (ws printer NI k) = B1 k) →
      (∀ x, x ≠ RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8 → (∀ k, ws printer NI k ≠ x) → B x = A1 x) →
      B = Tgt)
    (hRL : Step (RowsRowLevel.rowLevelMachine printer (rowsWork NI) ps) c1 H0 A0 H A1)
    (hW1 : Step (W1 NI iMode) n1 (fun _ => 0) B0 (fun _ => 0) (Function.update B0 (loopPort NI vL) w))
    (hW2 : Step (W2 NI iMode ini ix ib iOne iniS) n2 (fun _ => 0) (Function.update B0 (loopPort NI vL) w)
      (fun _ => 0) B1) :
    Step (Composition.machine (RowsRowLevel.rowLevelMachine printer (rowsWork NI) ps)
      (Composition.machine (RecoveryFocus.machine (ws printer NI) (W1 NI iMode))
        (Composition.machine (RecoveryFocus.machine (u6 printer NI)
            NearCubicWires.RepairSource.ProjectionNormalization.RawFrame.machine)
          (RecoveryFocus.machine (ws printer NI) (W2 NI iMode ini ix ib iOne iniS)))))
      (c1+1+(n1+1+((4*2^s+4)+1+n2))) H0 A0 H Tgt := by
  have st2 := w1_lift printer NI B0 w iMode n1 H A1 hbw rlw hW1
  have wne : ∀ k, k ≠ loopPort NI vL →
      Function.update A1 (ws printer NI (loopPort NI vL)) w (ws printer NI k) = B0 k := fun k hk => by
    rw [Function.update_of_ne (fun e => hk (ws_injective printer NI e)), rlw]
  have st3 := c6_lift printer NI caps B0 s w hwl hc60 hc61 H (Function.update A1 (ws printer NI (loopPort NI vL)) w)
    hbw hbf (Function.update_self _ _ _) wne
    (by rw [Function.update_of_ne (field_ne_ws printer NI 8 _), rl8])
  rw [hwl] at st3
  have a3w : ∀ k, Function.update (Function.update A1 (ws printer NI (loopPort NI vL)) w)
      (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) (ZeroPadding.pad caps.copyCap (frame w))
      (ws printer NI k) = Function.update B0 (loopPort NI vL) w k := fun k => by
    rw [Function.update_of_ne (fun e => field_ne_ws printer NI 8 k e.symm)]
    by_cases hk : k = loopPort NI vL
    · subst hk; rw [Function.update_self, Function.update_self]
    · rw [wne k hk, Function.update_of_ne hk]
  have st4 := w2_lift printer NI B0 B1 w iMode ini ix ib iOne iniS n2 H _ hbw a3w hW2
  have fin := hfin (install (ws printer NI) (Function.update (Function.update A1 (ws printer NI (loopPort NI vL)) w)
      (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)) 8) (ZeroPadding.pad caps.copyCap (frame w))) B1)
    (by rw [install_other _ _ _ _ (fun k e => field_ne_ws printer NI 8 k e.symm), Function.update_self])
    (fun k => by rw [install_slot _ (ws_injective printer NI)])
    (fun x hx8 hxw => by
      rw [install_other _ _ _ _ hxw, Function.update_of_ne hx8,
        Function.update_of_ne (fun e => hxw _ e.symm)])
  rw [fin] at st4
  exact hRL.seq (st2.seq (st3.seq st4))

/-- **`complete` on the row bank**, for any `base`: given the row-level step (rows-rowlevel `rowLevel_step`) and the two
work-block steps W1/W2 (`RowsCompleteRow`), the fixed `completeM` runs from `complete`'s entry bank of row `j` to the Frame
input bank of row `j` (`rowFrameIn_eq`'s right side), provided the verdict word IS field 8 of the row's datum. -/
theorem complete_row (hdrv : ∀ i, base i ps.drv = List.replicate caps.copyCap true)
    (hlg : ∀ i, base i ps.lg = List.replicate (caps.copyCap+1) false)
    (iMode : Fin NI) (ini : Fin 40 → Fin NI) (ix : Fin 4 → Fin NI) (ib : Fin 82 → Fin NI) (iOne : Fin NI)
    (iniS : Fin 9 → Fin NI) (s : Nat) (w : List Bool) (hwl : w.length = 2^s)
    (hw8 : w = RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) 8)
    (hc60 : base j.val (c6Port NI 0) = List.replicate (2^s) true)
    (hc61 : base j.val (c6Port NI 1) = List.replicate (2*2^s+1) false)
    (c1 n1 n2 : Nat)
    (hRL : Step (RowsRowLevel.rowLevelMachine printer (rowsWork NI) ps) c1
      (RowsRowLevel.entryH printer (rowsWork NI) a F g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) ps a F g layout caps reserve base j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out)
      (RowsRowLevel.rowLevelOut printer (rowsWork NI) ps a F g layout caps reserve base facts j out))
    (hW1 : Step (W1 NI iMode) n1 (fun _ => 0) (base j.val) (fun _ => 0)
      (Function.update (base j.val) (loopPort NI vL) w))
    (hW2 : Step (W2 NI iMode ini ix ib iOne iniS) n2 (fun _ => 0) (Function.update (base j.val) (loopPort NI vL) w)
      (fun _ => 0) (base (j.val+1))) :
    Step (completeM printer NI ps iMode ini ix ib iOne iniS) (c1+1+(n1+1+((4*2^s+4)+1+n2)))
      (RowsRowLevel.entryH printer (rowsWork NI) a F g layout j out)
      (RowsRowLevel.entryA printer (rowsWork NI) ps a F g layout caps reserve base j out)
      (PCJ45bee56da9f34d5a_RowState.headBank printer (rowsWork NI) a F g (j.val+1) out)
      (install (RowsRowLevel.fieldSlot printer (rowWork (rowsWork NI)))
        (PCJ45bee56da9f34d5a_RowState.bank printer (rowsWork NI) a F g layout caps reserve base ps.drv ps.lg
          (j.val+1) out)
        (fun k => ZeroPadding.pad caps.copyCap
          (frame (RowsRowLevel.fieldWord (RowsRowLevel.rowDatum a F g layout facts j) k)))) :=
  complete_gen printer NI ps caps (base j.val) (base (j.val+1)) iMode ini ix ib iOne iniS s w hwl hc60 hc61
    c1 n1 n2 _ _ _ _ _
    (fun k => hb_work printer NI a F g j out k) (hb_field printer NI a F g j out 8)
    (fun k => rl_work printer NI ps a F g layout caps reserve base facts j out hdrv hlg k)
    (rl_field8 printer NI ps a F g layout caps reserve base facts j out)
    (fun B h8 hwork hrest => RowsRowLevel.finish_eq printer (rowsWork NI) ps a F g layout caps reserve base facts j out B
      (by rw [h8, hw8]) (fun k => by rw [hwork, work_eq NI ps caps base hdrv hlg]) hrest)
    hRL hW1 hW2

end Row

end
end RowsConstruction.CompleteBank
