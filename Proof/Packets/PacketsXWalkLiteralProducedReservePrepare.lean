import Proof.Packets.PacketsXWalkLiteralProducedReserveData

/-! Ordinary executions create the two source templates and both reserve words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section
attribute [local irreducible] CycleCommonReserve.joined8 CyclePaletteReserve.joined8

theorem pool_run (C : Nat) (A : Fin 566→List Bool)
    (hc : A 40=List.replicate C true) (ht : A 434=[]) (hl : A 435=[]) :
    Step poolMachine (2*C+8) (fun _=>0) A (fun _=>0) (poolBank A C) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (DimensionTemplate.ready false C)) poolSlots (by decide)
    (fun _=>0) (fun _=>0) A (poolBank A C)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.input,poolSlots,hc,ht,hl]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.output,poolSlots,poolBank,hc]
  · intro i away
    have h434 : i≠434 := by intro he;exact away 1 (by simpa [poolSlots] using he.symm)
    have h435 : i≠435 := by intro he;exact away 2 (by simpa [poolSlots] using he.symm)
    exact ⟨rfl,by simp [poolBank,h434,h435]⟩

theorem width_run (w : Nat) (A : Fin 566→List Bool)
    (hc : A 433=List.replicate w true) (ht : A 436=[]) (hl : A 437=[]) :
    Step widthMachine (2*w+8) (fun _=>0) A (fun _=>0) (widthBank A w) := by
  apply PhysicalFocusBoundary.focus (CycleCommonReserve.of_clock (DimensionTemplate.ready false w)) widthSlots (by decide)
    (fun _=>0) (fun _=>0) A (widthBank A w)
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.input,widthSlots,hc,ht,hl]
  · intro i;rfl
  · intro i;fin_cases i <;>simp [DimensionTemplate.output,widthSlots,widthBank,hc]
  · intro i away
    have h436 : i≠436 := by intro he;exact away 1 (by simpa [widthSlots] using he.symm)
    have h437 : i≠437 := by intro he;exact away 2 (by simpa [widthSlots] using he.symm)
    exact ⟨rfl,by simp [widthBank,h436,h437]⟩

theorem templates_fresh (C w root population active n : Nat) (mask x y code : List Bool)
    (i : Fin 566) (hi : 438 ≤ i.val) : templates C w root population active n mask x y code i=[] := by
  have h434 : i≠434 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h435 : i≠435 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h436 : i≠436 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  have h437 : i≠437 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
  simp [templates,widthBank,poolBank,h434,h435,h436,h437,input,Fin.addCases,tailInput,
    show ¬i.val<433 by omega,show i.val-433≠0 by omega,Fin.ext_iff]

theorem common_join (C w root population active n : Nat) (mask x y code : List Bool) :
    ∀j,templates C w root population active n mask x y code (commonSlots j)=CycleCommonReserve.input C w j := by
  intro j
  by_cases h0 : j=0
  · subst j;simp [templates,widthBank,poolBank,commonSlots,CycleCommonReserve.input]
  by_cases h1 : j=1
  · subst j;simp [templates,widthBank,poolBank,commonSlots,CycleCommonReserve.input]
  by_cases h44 : j=44
  · subst j;rfl
  rw [commonSlots,if_neg h0,if_neg h1,if_neg h44,templates_fresh C w root population active n mask x y code
    ⟨438+j.val,by omega⟩ (by change 438 ≤ 438+j.val;omega)]
  simp [CycleCommonReserve.input,h0,h1]

theorem common_below (i : Fin 48) : (commonSlots i).val<486 := by
  have hi:=i.isLt
  unfold commonSlots
  split_ifs <;>norm_num
  omega

theorem common_away_S : ∀j,commonSlots j≠424 := by
  intro j he
  have hv:=congrArg Fin.val he
  unfold commonSlots at hv
  split_ifs at hv <;>norm_num at hv
  omega

theorem palette_join (C w root population active n : Nat) (mask x y code : List Bool) :
    ∀j,commonBank (templates C w root population active n mask x y code) C w (paletteSlots j)=CyclePaletteReserve.input C w j := by
  intro j
  by_cases h0 : j=0
  · subst j
    change install commonSlots _ _ (commonSlots 0)=_
    rw [install_slot commonSlots common_injective]
    exact common_pool_retained C w
  by_cases h1 : j=1
  · subst j
    change install commonSlots _ _ (commonSlots 1)=_
    rw [install_slot commonSlots common_injective]
    exact common_width_retained C w
  by_cases h76 : j=76
  · subst j
    rw [show paletteSlots 76=424 from rfl,commonBank,install_other _ _ _ _ common_away_S]
    rfl
  have away : ∀k,commonSlots k≠paletteSlots j := by
    intro k he
    have hb:=common_below k
    have hv:=congrArg Fin.val he
    simp only [paletteSlots,if_neg h0,if_neg h1,if_neg h76,Fin.val_mk] at hv
    omega
  rw [commonBank,install_other _ _ _ _ away]
  rw [paletteSlots,if_neg h0,if_neg h1,if_neg h76,templates_fresh C w root population active n mask x y code
    ⟨486+j.val,by omega⟩ (by change 438 ≤ 486+j.val;omega)]
  simp [CyclePaletteReserve.input,h0,h1]

theorem zero_heads {t : Nat} (slots : Fin t→Fin 566) : dockH slots (fun _=>0) (fun _=>0)=(fun _=>0) := by
  funext i;unfold dockH;cases RecoveryFocus.pick slots i <;>rfl

def setup := Composition.machine (Composition.machine (Composition.machine poolMachine widthMachine) commonMachine) paletteMachine
def setupBudget (C w : Nat) := 2*C+2*w+19+CycleCommonReserve.budget C w+CyclePaletteReserve.budget C w
attribute [local irreducible] poolMachine widthMachine commonMachine paletteMachine

theorem setup_run (C w root population active n : Nat) (mask x y code : List Bool) :
    Step setup (setupBudget C w) (fun _=>0) (input C w root population active n mask x y code)
      (fun _=>0) (prepared C w root population active n mask x y code) := by
  have first:=pool_run C (input C w root population active n mask x y code) rfl rfl rfl
  have second:=width_run w (poolBank (input C w root population active n mask x y code) C) rfl rfl rfl
  have third:=(CycleCommonReserve.run C w).focus commonSlots common_injective (fun _=>0)
    (templates C w root population active n mask x y code)
  have third':=(third.congr_in (zero_heads commonSlots)
    (install_existing _ _ _ (common_join C w root population active n mask x y code))).congr (zero_heads commonSlots) rfl
  have fourth:=(CyclePaletteReserve.run C w).focus paletteSlots palette_injective (fun _=>0)
    (commonBank (templates C w root population active n mask x y code) C w)
  have fourth':=(fourth.congr_in (zero_heads paletteSlots)
    (install_existing _ _ _ (palette_join C w root population active n mask x y code))).congr (zero_heads paletteSlots) rfl
  have joined:=((first.seq second).seq third').seq fourth'
  simpa only [setup,setupBudget,poolMachine,widthMachine,commonMachine,paletteMachine,prepared,commonBank,paletteBank,templates,
    show 2*C+8+1+(2*w+8)+1+CycleCommonReserve.budget C w+1+CyclePaletteReserve.budget C w=
      2*C+2*w+19+CycleCommonReserve.budget C w+CyclePaletteReserve.budget C w by omega] using joined

end
end Theorem25Completion.WalkLiteralProducedReserve
