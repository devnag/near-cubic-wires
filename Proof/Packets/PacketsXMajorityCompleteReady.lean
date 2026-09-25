import Proof.Packets.PacketsXMajorityCompleteCopy

/-! Exact boundary from the scalar and square producers to the reusable
majority initializer. No generated polynomial or execution is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion.CycleBounds Completion.SourceDock
noncomputable section

theorem copy_target_slot (i : Fin 10) :
    copySlots (((i.castAdd 1).natAdd 10).castAdd 1)=arenaSlots (i.castAdd 127) := by
  fin_cases i <;>rfl

theorem copied_master (C R n : Nat) (source : List Bool) (i : Fin 10) :
    afterCopy C R n source (arenaSlots (i.castAdd 127))=masters C R (n+1) (R^2) i := by
  rw [←copy_target_slot,afterCopy,install_slot copySlots copy_injective]
  simp only [NativeFanout.output,Fin.addCases_left,Fin.addCases_right,
    NativeFanout.word,identitySelect,Option.elim_some,masters]

theorem copied_source (C R n : Nat) (source : List Bool) : afterCopy C R n source 44=source := by
  rw [afterCopy,install_other copySlots _ _ _ (by decide),
    afterSquare,install_other widthSlots _ _ _ (by decide),
    afterScalar,install_other scalarSlots _ _ _ (by decide)]
  rfl

theorem copied_width (C R n : Nat) (source : List Bool) :
    afterCopy C R n source 134=UnaryTemplate.tape (R^2) := by
  rw [afterCopy,install_other copySlots _ _ _ (by decide)]
  change install widthSlots _ _ (widthSlots 7)=_
  rw [install_slot widthSlots width_injective]
  exact Width.square_template R

theorem copied_driver (C R n : Nat) (source : List Bool) :
    afterCopy C R n source 135=List.replicate (R^2) true := by
  change install copySlots _ _ (copySlots 20)=_
  rw [install_slot copySlots copy_injective]
  rfl

theorem copied_log (C R n : Nat) (source : List Bool) : afterCopy C R n source 136=[] := by
  rw [afterCopy,install_other copySlots _ _ _ (by decide),
    afterSquare,install_other widthSlots _ _ _ (by decide),
    afterScalar,install_other scalarSlots _ _ _ (by decide)]
  rfl

private theorem no_copy_private (i : Fin 178) (hlo : (10 : Nat) ≤ i.val) (hhi : i.val ≤ (133 : Nat)) :
    ∀j,copySlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  fin_cases j <;>simp only [copySlots,Matrix.cons_val_zero',Matrix.cons_val_succ'] at hv <;>omega
private theorem no_width_private (i : Fin 178) (hlo : (10 : Nat) ≤ i.val) (hhi : i.val ≤ (133 : Nat)) :
    ∀j,widthSlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  fin_cases j <;>simp only [widthSlots,Matrix.cons_val_zero',Matrix.cons_val_succ'] at hv <;>omega
private theorem no_scalar_private (i : Fin 178) (hhi : i.val ≤ (133 : Nat)) :
    ∀j,scalarSlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  dsimp only [scalarSlots] at hv
  omega

theorem copied_private (C R n : Nat) (source : List Bool) (i : Fin 123) :
    afterCopy C R n source (arenaSlots (Bootstrap.arenaSlots (Palette.privatePort i)))=[] := by
  have hlo : 10≤(arenaSlots (Bootstrap.arenaSlots (Palette.privatePort i))).val := by
    simp only [arenaSlots,Bootstrap.arenaSlots,Fin.val_castAdd,Fin.val_mk]
    omega
  have hhi : (arenaSlots (Bootstrap.arenaSlots (Palette.privatePort i))).val≤133 := by
    have ih:=i.isLt
    dsimp only [arenaSlots,Bootstrap.arenaSlots,Palette.privatePort,Fin.val_castAdd]
    split_ifs <;>simp only [Fin.val_mk] <;>omega
  have hn : Bootstrap.arenaSlots (Palette.privatePort i)≠44 := by
    intro he
    have hv:=congrArg Fin.val he
    have hne:=Palette.private_not_source i
    have hnval : (Palette.privatePort i).val≠34:=by intro h;exact hne (Fin.ext h)
    dsimp only [Bootstrap.arenaSlots] at hv
    omega
  rw [afterCopy,install_other copySlots _ _ _ (no_copy_private _ hlo hhi),
    afterSquare,install_other widthSlots _ _ _ (no_width_private _ hlo hhi),
    afterScalar,install_other scalarSlots _ _ _ (no_scalar_private _ hhi)]
  simp only [input,arenaSlots,Fin.append,Fin.addCases_left,if_neg hn]

theorem fanout_cover (i : Fin 137) (hs : i≠44) (hw : i≠134) :
    ∃j,Bootstrap.fanoutSlots j=i := by
  have hi:=i.isLt
  have hsval : i.val≠44:=by intro h;exact hs (Fin.ext h)
  have hwval : i.val≠134:=by intro h;exact hw (Fin.ext h)
  by_cases h : i.val<44
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp [Bootstrap.fanoutSlots,h]
  by_cases h' : i.val<134
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    simp only [Bootstrap.fanoutSlots,Fin.val_mk]
    rw [if_neg (by omega),if_pos (by omega)]
    dsimp
    omega
  · refine ⟨⟨i.val-2,by omega⟩,?_⟩
    apply Fin.ext
    simp only [Bootstrap.fanoutSlots,Fin.val_mk]
    rw [if_neg (by omega),if_neg (by omega)]
    dsimp
    omega

theorem copied_fanout_input (C R n : Nat) (source : List Bool) (i : Fin 135) :
    afterCopy C R n source (arenaSlots (Bootstrap.fanoutSlots i))=
      NativeFanout.input (m:=123) (masters C R (n+1) (R^2)) (R^2) i := by
  refine Fin.addCases (m:=134) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=10) (n:=124) (fun k=>?_) (fun k=>?_) j
    · have he : Bootstrap.fanoutSlots ((k.castAdd 124).castAdd 1)=k.castAdd 127 := by
        apply Fin.ext
        have hk:=k.isLt
        simp [Bootstrap.fanoutSlots,show k.val<44 by omega]
      rw [he,copied_master]
      simp only [NativeFanout.input,Fin.addCases_left]
    · refine Fin.addCases (m:=123) (n:=1) (fun k=>?_) (fun k=>?_) k
      · rw [Bootstrap.target_slot,copied_private]
        simp only [NativeFanout.input,Fin.addCases_left,Fin.addCases_right]
      · fin_cases k
        exact copied_driver C R n source
  · fin_cases j
    exact copied_log C R n source

theorem initialize_input (C R n : Nat) (source : List Bool) :
    (fun i=>afterCopy C R n source (arenaSlots i))=
      Bootstrap.cold (masters C R (n+1) (R^2)) (R^2) source := by
  funext i
  by_cases hs : i=44
  · subst i
    rw [Bootstrap.cold,install_other Bootstrap.fanoutSlots _ _ _ Bootstrap.fanout_not_source]
    exact copied_source C R n source
  by_cases hw : i=134
  · subst i
    rw [Bootstrap.cold,install_other Bootstrap.fanoutSlots _ _ _ Bootstrap.fanout_not_width]
    exact copied_width C R n source
  obtain ⟨j,rfl⟩:=fanout_cover i hs hw
  rw [Bootstrap.cold,install_slot Bootstrap.fanoutSlots Bootstrap.fanout_injective]
  exact copied_fanout_input C R n source j

theorem initialize_heads (i : Fin 137) : widthHeads (arenaSlots i)=Bootstrap.baseH i := by
  have all : ∀i:Fin 137,widthHeads (arenaSlots i)=Bootstrap.baseH i := by decide
  exact all i

theorem initialize_run (C w n : Nat) (ps : List (Ring.Poly Nat)) (hlen : ps.length=n+1)
    (hN : n+1≤2^w) (hCodes : 2^(n+1)≤2^w) (hw : 1≤w) :
    Step initializeMachine (2*(commonReserve C w)^2+6) widthHeads
      (afterCopy C (commonReserve C w) n (OrderedPacketStep.bank C (commonReserve C w) ps))
      resultHeads (result C (commonReserve C w) n ps) := by
  have h:=Bootstrap.boot_ready_with (masters C (commonReserve C w) (n+1) ((commonReserve C w)^2))
    C w ps (by simpa only [hlen] using hN) (by simpa only [hlen] using hCodes) hw
    (by simpa only [hlen] using actual_compatible C w (n+1) hCodes)
  exact Completion.SourceDock.dock h arenaSlots arena_injective widthHeads _ initialize_heads
    (congrFun (initialize_input C (commonReserve C w) n (OrderedPacketStep.bank C (commonReserve C w) ps)))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
