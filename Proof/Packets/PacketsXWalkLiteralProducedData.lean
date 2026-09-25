import Proof.Packets.PacketsXWalkLiteralMastersGraded
import Proof.Packets.PacketsXWalkLiteralProgram

/-! The global producer-to-walk wiring. The only external words are raw scalar
inputs, the actual mask, two unpadded coordinate frames, transition labels,
the separately generated capacity driver, and the repetition word. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

def paletteSlots : Fin 15→Fin 95 := ![81,82,71,41,83,84,85,86,87,88,89,90,91,92,93]
theorem palette_slots_original (i : Fin 15) : paletteSlots i=
    WalkLiteralMasters.gradedSlots (WalkLiteralMasters.paletteSlots i) := by fin_cases i <;>rfl

def coldSlots (i : Fin 333) : Fin 433 :=
  if h : (15 ≤ i.val ∧ i.val < 30) then
    (paletteSlots ⟨i.val-15,by omega⟩).castAdd 338 else ⟨95+i.val,by omega⟩

theorem cold_slots_injective : Function.Injective coldSlots := by
  have hp : Function.Injective paletteSlots := by decide
  intro i j hij
  unfold coldSlots at hij
  split_ifs at hij with hi hj hj
  · have he := hp (Fin.castAdd_inj.mp hij)
    have hv := congrArg Fin.val he
    apply Fin.ext;dsimp at hv;omega
  · have hv := congrArg Fin.val hij
    have hb := (paletteSlots ⟨i.val-15,by omega⟩).isLt
    dsimp at hv;omega
  · have hv := congrArg Fin.val hij
    have hb := (paletteSlots ⟨j.val-15,by omega⟩).isLt
    dsimp at hv;omega
  · have hv := congrArg Fin.val hij
    apply Fin.ext;dsimp at hv;omega

def extras (S n : Nat) (x y code : List Bool) (i : Fin 338) : List Bool :=
  if i=7 then code else if i=329 then List.replicate S true else
  if i=332 then CompareMachine.word n else if i=333 then x else if i=334 then y else []
def bank0 (masters : Fin 95→List Bool) (S n : Nat) (x y code : List Bool) : Fin 433→List Bool :=
  Fin.addCases (m:=95) (n:=338) (motive:=fun _=>List Bool) masters (extras S n x y code)
def input (C R root population active S n : Nat) (mask x y code : List Bool) :=
  bank0 (WalkLiteralMasters.gradedInput C R root population active mask) S n x y code

def rawSlots : Fin 3→Fin 433 := ![71,99,430]
def templateSlots : Fin 3→Fin 433 := ![99,100,431]
def fanoutSlots : Fin 8→Fin 433 := ![88,428,429,105,95,96,41,432]
def select : Fin 3→Option (Fin 3) := ![some 0,some 1,some 2]
def rawMachine := RecoveryFocus.machine rawSlots (UWalkUnary.machine false false)
def templateMachine := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def fanoutMachine := RecoveryFocus.machine fanoutSlots (NativeFanout.machine select)
def rawBank (A : Fin 433→List Bool) (R : Nat) :=
  Function.update (Function.update A (99 : Fin 433) (List.replicate R true)) 430 (List.replicate (R+2) false)
def templateBank (A : Fin 433→List Bool) (R : Nat) :=
  Function.update (Function.update A (100 : Fin 433) (UnaryTemplate.tape R)) 431 (List.replicate (R+3) false)
def fanoutSource (rank R : Nat) (x y : List Bool) : Fin 3→List Bool :=
  ![ZeroPadding.pad R (UnaryTemplate.tape rank),x,y]
def fanoutBank (A : Fin 433→List Bool) (rank R : Nat) (x y : List Bool) :=
  Function.update (Function.update (Function.update (Function.update A
    (105 : Fin 433) (ZeroPadding.pad R (UnaryTemplate.tape rank)))
    95 (ZeroPadding.pad R x)) 96 (ZeroPadding.pad R y)) 432 (List.replicate (R+1) false)
def prepared (masters : Fin 95→List Bool) (rank R S n : Nat) (x y code : List Bool) :=
  fanoutBank (templateBank (rawBank (bank0 masters S n x y code) R) R) rank R x y

def countSlots (_ : Fin 1) : Fin 433 := 427
def countRaise := RecoveryFocus.machine countSlots (PhysicalDriverMoves.machine 1 .right)
def preparedHeads : Fin 433→Nat := Function.update (fun _=>0) 427 1

theorem pad_idem (R : Nat) (xs : List Bool) :
    ZeroPadding.pad R (ZeroPadding.pad R xs)=ZeroPadding.pad R xs := by
  simp [ZeroPadding.pad,ZeroPadding.pad_length]
  omega

theorem unary_source (R : Nat) : UWalkUnary.source (R+2) R=UnaryTemplate.tape R := by
  rw [UWalkUnary.source,CycleLiveSuccessor.pad_compare_template (R+2) R (by omega)]
  simp [ZeroPadding.pad,UnaryTemplate.tape]

end
end Theorem25Completion.WalkLiteralProduced
