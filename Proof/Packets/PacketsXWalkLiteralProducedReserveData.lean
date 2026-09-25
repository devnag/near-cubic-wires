import Proof.Packets.PacketsXWalkLiteralProducedRun
import Proof.Packets.CyclePaletteReserve

/-! Both walk reserves are physically generated from raw pool and width words.
The existing433-tape produced-walk layout occupies the first433 ports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

abbrev R (C w : Nat) := CycleBounds.commonReserve C w
abbrev S (C w : Nat) := CyclePaletteReserve.reserve C w

def tailInput (w : Nat) (i : Fin 133) : List Bool := if i=0 then List.replicate w true else []
def input (C w root population active n : Nat) (mask x y code : List Bool) : Fin 566→List Bool :=
  Fin.addCases (m:=433) (n:=133) (motive:=fun _=>List Bool)
    (WalkLiteralProduced.input C 0 root population active 0 n mask x y code) (tailInput w)
def poolSlots : Fin 3→Fin 566 := ![40,434,435]
def widthSlots : Fin 3→Fin 566 := ![433,436,437]
def commonSlots (i : Fin 48) : Fin 566 :=
  if i=0 then 434 else if i=1 then 436 else if i=44 then 41 else ⟨438+i.val,by omega⟩
def paletteSlots (i : Fin 80) : Fin 566 :=
  if i=0 then 434 else if i=1 then 436 else if i=76 then 424 else ⟨486+i.val,by omega⟩

def poolMachine := RecoveryFocus.machine poolSlots (DimensionTemplate.machine false)
def widthMachine := RecoveryFocus.machine widthSlots (DimensionTemplate.machine false)
def commonMachine := RecoveryFocus.machine commonSlots CycleCommonReserve.machine
def paletteMachine := RecoveryFocus.machine paletteSlots CyclePaletteReserve.machine

def poolBank (A : Fin 566→List Bool) (C : Nat) :=
  Function.update (Function.update A (434 : Fin 566) (UnaryTemplate.tape C)) 435 (List.replicate (C+3) false)
def widthBank (A : Fin 566→List Bool) (w : Nat) :=
  Function.update (Function.update A (436 : Fin 566) (UnaryTemplate.tape w)) 437 (List.replicate (w+3) false)
def templates (C w root population active n : Nat) (mask x y code : List Bool) :=
  widthBank (poolBank (input C w root population active n mask x y code) C) w
def commonBank (A : Fin 566→List Bool) (C w : Nat) := install commonSlots A (CycleCommonReserve.output C w)
def paletteBank (A : Fin 566→List Bool) (C w : Nat) := install paletteSlots A (CyclePaletteReserve.output C w)
def prepared (C w root population active n : Nat) (mask x y code : List Bool) :=
  paletteBank (commonBank (templates C w root population active n mask x y code) C w) C w

theorem common_injective : Function.Injective commonSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  unfold commonSlots at hv
  split_ifs at hv <;>first | omega | (apply Fin.ext;dsimp at hv;omega)

theorem palette_injective : Function.Injective paletteSlots := by
  intro i j he
  have hv:=congrArg Fin.val he
  unfold paletteSlots at hv
  split_ifs at hv <;>first | omega | (apply Fin.ext;dsimp at hv;omega)

theorem common_pool_retained (C w : Nat) : CycleCommonReserve.output C w 0=UnaryTemplate.tape C := by
  change CycleCommonReserve.bank8 C w 0=_
  rw [CycleCommonReserve.bank8_other C w 0 (by decide),CycleCommonReserve.bank7_other C w 0 (by decide),
    CycleCommonReserve.bank6_other C w 0 (by decide),CycleCommonReserve.bank5_other C w 0 (by decide),
    CycleCommonReserve.bank4_other C w 0 (by decide),CycleCommonReserve.bank3_other C w 0 (by decide),
    CycleCommonReserve.bank2_other C w 0 (by decide)]
  change CycleCommonReserve.bank1 C w (CycleCommonReserve.slots1 0)=_
  rw [CycleCommonReserve.bank1_slot]
  exact CycleLiveSuccessor.source_eq C

theorem common_width_retained (C w : Nat) : CycleCommonReserve.output C w 1=UnaryTemplate.tape w := by
  change CycleCommonReserve.bank8 C w 1=_
  rw [CycleCommonReserve.bank8_other C w 1 (by decide),CycleCommonReserve.bank7_other C w 1 (by decide),
    CycleCommonReserve.bank6_other C w 1 (by decide),CycleCommonReserve.bank5_other C w 1 (by decide)]
  change CycleCommonReserve.bank4 C w (CycleCommonReserve.slots4 0)=_
  rw [CycleCommonReserve.bank4_slot]
  exact CycleLiveSuccessor.source_eq w

end
end Theorem25Completion.WalkLiteralProducedReserve
