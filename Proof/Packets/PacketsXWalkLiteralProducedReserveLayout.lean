import Proof.Packets.PacketsXWalkLiteralProducedReserveData

/-! The two physically written reserve words supply exactly the earlier433
port entry; all other source and sample words keep their original placement. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] CycleCommonReserve.bank8 CyclePaletteReserve.bank8

theorem input_R (C R0 R1 root population active S n : Nat) (mask x y code : List Bool) :
    Function.update (WalkLiteralProduced.input C R0 root population active S n mask x y code)
      (41 : Fin 433) (List.replicate R1 true)=
      WalkLiteralProduced.input C R1 root population active S n mask x y code := by
  unfold WalkLiteralProduced.input WalkLiteralProduced.bank0
  change Function.update (Fin.addCases (m:=95) (n:=338) (motive:=fun _=>List Bool)
    (WalkLiteralMasters.gradedInput C R0 root population active mask) (WalkLiteralProduced.extras S n x y code))
    ((41 : Fin 95).castAdd 338) (List.replicate R1 true)=_
  rw [PhysicalAppendUpdate.left]
  congr 1
  unfold WalkLiteralMasters.gradedInput
  change Function.update (Fin.addCases (m:=40) (n:=55) (motive:=fun _=>List Bool)
    (SourceGradedRank.input population active) (WalkLiteralMasters.gradedExtra C R0 root mask))
    ((1 : Fin 55).natAdd 40) (List.replicate R1 true)=_
  rw [PhysicalAppendUpdate.right]
  congr 1
  funext i
  by_cases hi : i=1
  · subst i;simp [WalkLiteralMasters.gradedExtra]
  · simp [WalkLiteralMasters.gradedExtra,hi]

theorem input_S (C R root population active S0 S1 n : Nat) (mask x y code : List Bool) :
    Function.update (WalkLiteralProduced.input C R root population active S0 n mask x y code)
      (424 : Fin 433) (List.replicate S1 true)=
      WalkLiteralProduced.input C R root population active S1 n mask x y code := by
  unfold WalkLiteralProduced.input WalkLiteralProduced.bank0
  change Function.update (Fin.addCases (m:=95) (n:=338) (motive:=fun _=>List Bool)
    (WalkLiteralMasters.gradedInput C R root population active mask) (WalkLiteralProduced.extras S0 n x y code))
    ((329 : Fin 338).natAdd 95) (List.replicate S1 true)=_
  rw [PhysicalAppendUpdate.right]
  congr 1
  funext i
  by_cases hi : i=329
  · subst i;simp [WalkLiteralProduced.extras]
  · simp [WalkLiteralProduced.extras,hi]

theorem input_resources (C R root population active S n : Nat) (mask x y code : List Bool) :
    Function.update (Function.update (WalkLiteralProduced.input C 0 root population active 0 n mask x y code)
      (41 : Fin 433) (List.replicate R true)) 424 (List.replicate S true)=
      WalkLiteralProduced.input C R root population active S n mask x y code := by
  rw [input_R,input_S]

theorem templates_small (C w root population active n : Nat) (mask x y code : List Bool) (i : Fin 433) :
    templates C w root population active n mask x y code (i.castAdd 133)=
      WalkLiteralProduced.input C 0 root population active 0 n mask x y code i := by
  have hi:=i.isLt
  have h434 : i.castAdd 133≠(434 : Fin 566) := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h435 : i.castAdd 133≠(435 : Fin 566) := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h436 : i.castAdd 133≠(436 : Fin 566) := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h437 : i.castAdd 133≠(437 : Fin 566) := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  simp only [templates,widthBank,poolBank,Function.update_of_ne h434,Function.update_of_ne h435,
    Function.update_of_ne h436,Function.update_of_ne h437,input,Fin.addCases_left]

theorem common_small_away (i : Fin 433) (hi : i≠41) : ∀j,commonSlots j≠i.castAdd 133 := by
  have bound:=i.isLt
  have different : i.val≠41 := by
    intro he
    apply hi
    exact Fin.ext he
  intro j he
  have hv:=congrArg Fin.val he
  unfold commonSlots at hv
  split_ifs at hv <;>norm_num at hv <;>omega

theorem palette_small_away (i : Fin 433) (hi : i≠424) : ∀j,paletteSlots j≠i.castAdd 133 := by
  have bound:=i.isLt
  have different : i.val≠424 := by
    intro he
    apply hi
    exact Fin.ext he
  intro j he
  have hv:=congrArg Fin.val he
  unfold paletteSlots at hv
  split_ifs at hv <;>norm_num at hv <;>omega

theorem commonBank_R (A : Fin 566→List Bool) (C w : Nat) :
    commonBank A C w 41=List.replicate (R C w) true := by
  have hs : commonSlots 44=(41 : Fin 566) := rfl
  rw [commonBank,←hs,install_slot commonSlots common_injective]
  exact CycleCommonReserve.raw_reserve C w

theorem paletteBank_R (A : Fin 566→List Bool) (C w : Nat) :
    paletteBank A C w 41=A 41 := by
  have away : ∀j,paletteSlots j≠(41 : Fin 566) := palette_small_away 41 (by decide)
  exact install_other paletteSlots A (CyclePaletteReserve.output C w) 41 away

theorem paletteBank_S (A : Fin 566→List Bool) (C w : Nat) :
    paletteBank A C w 424=List.replicate (S C w) true := by
  have hs : paletteSlots 76=(424 : Fin 566) := rfl
  rw [paletteBank,←hs,install_slot paletteSlots palette_injective]
  exact CyclePaletteReserve.raw_reserve C w

theorem prepared_R (C w root population active n : Nat) (mask x y code : List Bool) :
    prepared C w root population active n mask x y code 41=List.replicate (R C w) true := by
  rw [prepared,paletteBank_R,commonBank_R]

theorem prepared_S (C w root population active n : Nat) (mask x y code : List Bool) :
    prepared C w root population active n mask x y code 424=List.replicate (S C w) true := by
  rw [prepared,paletteBank_S]

theorem prepared_other (C w root population active n : Nat) (mask x y code : List Bool)
    (i : Fin 433) (h41 : i≠41) (h424 : i≠424) :
    prepared C w root population active n mask x y code (i.castAdd 133)=
      WalkLiteralProduced.input C 0 root population active 0 n mask x y code i := by
  rw [prepared,paletteBank,install_other _ _ _ _ (palette_small_away i h424),
    commonBank,install_other _ _ _ _ (common_small_away i h41),templates_small]

/-- A pointwise resource substitution, independent of the reserve implementation. -/
theorem view_update (A : Fin 566→List Bool) (B : Fin 433→List Bool) (r s : List Bool)
    (hr : A 41=r) (hs : A 424=s)
    (other : ∀i : Fin 433,i≠41→i≠424→A (i.castAdd 133)=B i) :
    ∀i : Fin 433,A (i.castAdd 133)=Function.update (Function.update B 41 r) 424 s i := by
  intro i
  by_cases h41 : i=41
  · subst i
    simpa only [Function.update_of_ne (show (41 : Fin 433)≠424 by decide),Function.update_self] using (Eq.trans (congrArg A (show (41 : Fin 433).castAdd 133=(41 : Fin 566) by decide)) hr)
  by_cases h424 : i=424
  · subst i
    simpa only [Function.update_self] using (Eq.trans (congrArg A (show (424 : Fin 433).castAdd 133=(424 : Fin 566) by decide)) hs)
  simpa only [Function.update_of_ne h41,Function.update_of_ne h424] using other i h41 h424

theorem prepared_view (C w root population active n : Nat) (mask x y code : List Bool) :
    ∀i,prepared C w root population active n mask x y code (i.castAdd 133)=
      WalkLiteralProduced.input C (R C w) root population active (S C w) n mask x y code i := by
  have hv:=view_update (prepared C w root population active n mask x y code)
    (WalkLiteralProduced.input C 0 root population active 0 n mask x y code)
    (List.replicate (R C w) true) (List.replicate (S C w) true)
    (prepared_R C w root population active n mask x y code)
    (prepared_S C w root population active n mask x y code)
    (prepared_other C w root population active n mask x y code)
  intro i
  exact (hv i).trans (congrFun (input_resources C (R C w) root population active (S C w) n mask x y code) i)

end
end Theorem25Completion.WalkLiteralProducedReserve
