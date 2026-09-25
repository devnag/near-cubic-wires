import Proof.MachineModel.ClosureLocalSupport
import Proof.Packets.PacketsXLiteralPairUnary
import Proof.Rows.PhysicalDriverMoves

/-! Reusable unary literal-pair emission. The append port is protected while
all 55 private tapes and the actual reset log are physically cleared. Unary
metadata are retained, and the descending index cursor returns to one. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairReusable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion
noncomputable section

def cap (R : Nat) (i : Fin 58) : Nat := if i=2 then 0 else R
def selected (i : Fin 58) : Bool := decide (i≠2)
def padded (R : Nat) (a : Fin 58→List Bool) (i : Fin 58) := ZeroPadding.pad (cap R i) (a i)
def bank (R tag index : Nat) (pre : List Bool) (i : Fin 61) : List Bool :=
  if i=0 then UWalkUnary.source R tag else if i=1 then UWalkUnary.source R index
  else if i=2 then pre else if i=59 then List.replicate R true
  else if i=60 then List.replicate (R+3) false else List.replicate R false
def heads0 (pre : List Bool) (i : Fin 61) : Nat := if i=2 then pre.length else 0
def heads (pre : List Bool) (i : Fin 61) : Nat :=
  if i=1 then 1 else heads0 pre i

def middle (R tag index : Nat) (pre : List Bool) : Fin 61→List Bool :=
  Fin.addCases (m:=59) (n:=2) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=58) (n:=1) (motive:=fun _=>List Bool)
      (padded R (LiteralPairUnary.output R tag index pre)) (fun _=>List.replicate R false))
    (![List.replicate R true,List.replicate (R+3) false])
def scratchSlots (i : Fin 56) : Fin 61 := ⟨i.val+3,by omega⟩
def eraseSlots : Fin 58→Fin 61 := Fin.addCases (m:=56) (n:=2) scratchSlots (![59,60])
theorem erase_injective : Function.Injective eraseSlots := by decide
def backing (R tag index : Nat) (pre : List Bool) (i : Fin 56) :=
  middle R tag index pre (scratchSlots i)
def cleared (R : Nat) : Fin 58→List Bool := Fin.addCases (m:=57) (n:=1) (motive:=fun _=>List Bool)
  (Fin.addCases (m:=56) (n:=1) (motive:=fun _=>List Bool)
    (fun _=>List.replicate R false) (fun _=>List.replicate R true))
  (fun _=>List.replicate (R+3) false)
def erased (R tag index : Nat) (pre : List Bool) :=
  install eraseSlots (middle R tag index pre) (cleared R)

def worker := TapeEmbedding.machine 2 (MaskedReset.machine LiteralPairUnary.machine selected)
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 56)
def indexSlot : Fin 1→Fin 61 := ![1]
def left := RecoveryFocus.machine indexSlot (PhysicalDriverMoves.machine 1 .left)
def right := RecoveryFocus.machine indexSlot (PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine (Composition.machine (Composition.machine left worker) erase) right
def budget (R tag index : Nat) := 2*LiteralPairUnary.budget R tag index+2*R+11

theorem pad_twice (R : Nat) (xs : List Bool) : ZeroPadding.pad R (ZeroPadding.pad R xs)=ZeroPadding.pad R xs := by
  change ZeroPadding.pad R xs ++ List.replicate (R-(ZeroPadding.pad R xs).length) false=_
  rw [ZeroPadding.pad_length,Nat.sub_eq_zero_of_le (Nat.le_max_left _ _)]
  simp

theorem worker_run (R tag index : Nat) (pre : List Bool)
    (hR : LiteralPairUnary.budget R tag index≤R) :
    Step worker (2*LiteralPairUnary.budget R tag index+2)
      (heads0 pre) (bank R tag index pre)
      (heads0 (LiteralPairUnary.next tag index pre)) (middle R tag index pre) := by
  have h := (((LiteralPairUnary.run R tag index pre).pad (cap R)).mask selected
    (by intro i hi;have hn : i≠2 := by simpa [selected] using hi
        simp [LiteralPairUnary.heads,hn]) (cap:=R) hR).embed
      (fun _ : Fin 2=>0) (![List.replicate R true,List.replicate (R+3) false])
  have hin : (Fin.addCases (m:=59) (n:=2) (motive:=fun _=>Nat)
      (Fin.addCases (m:=58) (n:=1) (motive:=fun _=>Nat) (LiteralPairUnary.heads pre) (fun _=>0))
      (fun _=>0))=heads0 pre := by funext i;fin_cases i <;>rfl
  have hout : (Fin.addCases (m:=59) (n:=2) (motive:=fun _=>Nat)
      (Fin.addCases (m:=58) (n:=1) (motive:=fun _=>Nat)
        (fun i=>if selected i then 0 else LiteralPairUnary.heads (LiteralPairUnary.next tag index pre) i)
        (fun _=>0)) (fun _=>0))=heads0 (LiteralPairUnary.next tag index pre) := by
    funext i;fin_cases i <;>rfl
  have tins : (Fin.addCases (m:=59) (n:=2) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=58) (n:=1) (motive:=fun _=>List Bool)
        (padded R (LiteralPairUnary.input R tag index pre)) (fun _=>List.replicate R false))
      (![List.replicate R true,List.replicate (R+3) false]))=bank R tag index pre := by
    funext i
    fin_cases i
    all_goals simp [Fin.addCases,padded,cap,LiteralPairUnary.input,bank,UWalkUnary.source,pad_twice,
      ZeroPadding.pad_zero]
    all_goals rfl
  exact (h.congr_in hin tins).congr hout rfl

theorem private_fits (R tag index : Nat) (pre : List Bool)
    (hR : LiteralPairUnary.budget R tag index+1≤R) :
    ∀ i : Fin 58,i.val≥3→(padded R (LiteralPairUnary.output R tag index pre) i).length≤R := by
  intro i hi
  have hn : i≠2 := by intro h;subst i;omega
  have hinput : (LiteralPairUnary.input R tag index pre i).length≤R := by
    simp [LiteralPairUnary.input,show i≠0 by intro h;subst i;omega,
      show i≠1 by intro h;subst i;omega,hn]
  have hheads : LiteralPairUnary.heads pre i=0 := by simp [LiteralPairUnary.heads,hn]
  have fit := P1Closure.LocalSupport.step_fits (LiteralPairUnary.run R tag index pre) i R
    hinput (by rw [hheads,Nat.zero_add];exact hR)
  simp [padded,cap,hn,ZeroPadding.pad_length,Nat.max_eq_left fit]

theorem backing_fits (R tag index : Nat) (pre : List Bool)
    (hR : LiteralPairUnary.budget R tag index+1≤R) : ∀ i,(backing R tag index pre i).length≤R := by
  intro i
  by_cases hi : i.val<55
  · let j : Fin 58 := ⟨i.val+3,by omega⟩
    change (middle R tag index pre ((j.castAdd 1).castAdd 2)).length≤R
    simp only [middle,Fin.addCases_left]
    exact private_fits R tag index pre hR j (by dsimp [j];omega)
  · have he : i=55 := Fin.ext (by omega)
    subst i
    change (List.replicate R false).length≤R
    simp

theorem erase_run (R tag index : Nat) (pre : List Bool)
    (hR : LiteralPairUnary.budget R tag index+1≤R) :
    Step erase (2*R+4) (heads0 (LiteralPairUnary.next tag index pre)) (middle R tag index pre)
      (heads0 (LiteralPairUnary.next tag index pre)) (erased R tag index pre) := by
  have small := Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (backing R tag index pre) (backing_fits R tag index pre hR))
  rw [Nat.max_eq_left (by omega : R+1≤R+3)] at small
  apply PhysicalFocusBoundary.focus small eraseSlots erase_injective
    (heads0 (LiteralPairUnary.next tag index pre)) _ (middle R tag index pre) (erased R tag index pre)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;exact (install_slot eraseSlots erase_injective _ _ i).symm
  · intro i hi
    exact ⟨rfl,(install_other eraseSlots _ _ i hi).symm⟩

theorem erased_eq (R tag index : Nat) (pre : List Bool) :
    erased R tag index pre=bank R tag index (LiteralPairUnary.next tag index pre) := by
  have htag : erased R tag index pre 0=UWalkUnary.source R tag := by
    rw [erased,install_other eraseSlots _ _ 0 (by decide)]
    change ZeroPadding.pad R (LiteralPairUnary.output R tag index pre 0)=_
    rw [LiteralPairUnary.tag_out]
    exact pad_twice R _
  have hind : erased R tag index pre 1=UWalkUnary.source R index := by
    rw [erased,install_other eraseSlots _ _ 1 (by decide)]
    change ZeroPadding.pad R (LiteralPairUnary.output R tag index pre 1)=_
    rw [LiteralPairUnary.index_out]
    exact pad_twice R _
  have hout : erased R tag index pre 2=LiteralPairUnary.next tag index pre := by
    rw [erased,install_other eraseSlots _ _ 2 (by decide)]
    change ZeroPadding.pad 0 (LiteralPairUnary.output R tag index pre 2)=_
    rw [ZeroPadding.pad_zero,LiteralPairUnary.record_out]
  funext i
  fin_cases i
  · exact htag
  · exact hind
  · exact hout
  all_goals first
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 0
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 1
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 2
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 3
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 4
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 5
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 6
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 7
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 8
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 9
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 10
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 11
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 12
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 13
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 14
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 15
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 16
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 17
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 18
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 19
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 20
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 21
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 22
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 23
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 24
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 25
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 26
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 27
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 28
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 29
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 30
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 31
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 32
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 33
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 34
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 35
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 36
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 37
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 38
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 39
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 40
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 41
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 42
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 43
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 44
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 45
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 46
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 47
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 48
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 49
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 50
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 51
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 52
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 53
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 54
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 55
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 56
    | exact install_slot eraseSlots erase_injective (middle R tag index pre) (cleared R) 57

theorem cursor_step (goRight : Bool) (R tag index : Nat) (pre : List Bool) :
    Step (if goRight then right else left) 1
      (if goRight then heads0 pre else heads pre) (bank R tag index pre)
      (if goRight then heads pre else heads0 pre) (bank R tag index pre) := by
  cases goRight
  · have small:=PhysicalDriverMoves.run HeadMove.left (fun _ : Fin 1=>1)
      (fun _ : Fin 1=>UWalkUnary.source R index)
    apply PhysicalFocusBoundary.focus small indexSlot (by decide)
      (heads pre) (heads0 pre) (bank R tag index pre) (bank R tag index pre)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i hi
      have hn : i≠1 := by intro h;subst i;exact hi 0 rfl
      exact ⟨by simp [heads,hn],rfl⟩
  · have small:=PhysicalDriverMoves.run HeadMove.right (fun _ : Fin 1=>0)
      (fun _ : Fin 1=>UWalkUnary.source R index)
    apply PhysicalFocusBoundary.focus small indexSlot (by decide)
      (heads0 pre) (heads pre) (bank R tag index pre) (bank R tag index pre)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i hi
      have hn : i≠1 := by intro h;subst i;exact hi 0 rfl
      exact ⟨by simp [heads,hn],rfl⟩

theorem run (R tag index : Nat) (pre : List Bool)
    (hR : LiteralPairUnary.budget R tag index+1≤R) :
    Step machine (budget R tag index) (heads pre) (bank R tag index pre)
      (heads (LiteralPairUnary.next tag index pre))
      (bank R tag index (LiteralPairUnary.next tag index pre)) := by
  have eraseReady := (erase_run R tag index pre hR).congr rfl (erased_eq R tag index pre)
  have h := (((cursor_step false R tag index pre).seq
    (worker_run R tag index pre (by omega))).seq eraseReady).seq
    (cursor_step true R tag index (LiteralPairUnary.next tag index pre))
  convert h using 1 <;>first | rfl | (unfold budget;omega)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairReusable
