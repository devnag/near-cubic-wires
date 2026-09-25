import Proof.Packets.PacketsXLiteralCache

/-! Paid between-cache preparation. Every private tape is physically cleared,
then actual resident tag/count templates are copied into the metadata and
counted-loop driver. The cache output has reserved zero backing on reentry. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReload
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization Completion
noncomputable section

def input (R tag count : Nat) (b : Fin 68→List Bool) (i : Fin 68) : List Bool :=
  if i=59 then List.replicate R true else if i=60 then List.replicate (R+3) false
  else if i=62 then UnaryTemplate.tape R else if i=64 then UnaryTemplate.tape tag
  else if i=65 then UnaryTemplate.tape count else b i

def cleared (R tag count : Nat) := input R tag count (fun _=>List.replicate R false)
def bank3 (R tag count : Nat) (i : Fin 68) :=
  if i=0 then UWalkUnary.source R tag else cleared R tag count i
def bank4 (R tag count : Nat) (i : Fin 68) :=
  if i=1 then UWalkUnary.source R count else bank3 R tag count i
def ready (R tag count : Nat) (i : Fin 68) :=
  if i=61 then UWalkUnary.source R count else bank4 R tag count i
def resetHeads (i : Fin 68) : Nat := if i=62 then 1 else 0
abbrev heads := LiteralCacheAllocate.heads

def scratchSlots (i : Fin 63) : Fin 68 :=
  if h : i.val<59 then ⟨i.val,by omega⟩ else (![61,63,66,67] : Fin 4→Fin 68) ⟨i.val-59,by omega⟩
def clearSlots : Fin 65→Fin 68 := Fin.addCases (m:=63) (n:=2) scratchSlots (![59,60])
def moveSlots : Fin 2→Fin 68 := ![1,61]
def tagSlots : Fin 3→Fin 68 := ![64,0,63]
def indexSlots : Fin 3→Fin 68 := ![65,1,66]
def driverSlots : Fin 3→Fin 68 := ![65,61,67]
def phase1 := RecoveryFocus.machine moveSlots (PhysicalDriverMoves.machine 2 .left)
def phase2 := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 63)
def phase3 := RecoveryFocus.machine tagSlots (UWalkUnary.machine true false)
def phase4 := RecoveryFocus.machine indexSlots (UWalkUnary.machine true false)
def phase5 := RecoveryFocus.machine driverSlots (UWalkUnary.machine true false)
def phase6 := RecoveryFocus.machine moveSlots (PhysicalDriverMoves.machine 2 .right)
def machine := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine phase1 phase2) phase3) phase4) phase5) phase6
def budget (R tag count : Nat) := 2*R+2*tag+4*count+29

theorem local_copy (R n : Nat) (h : n+2≤R) : Step (UWalkUnary.machine true false) (2*n+6)
    (fun _=>0) ![UnaryTemplate.tape n,List.replicate R false,List.replicate R false]
    (fun _=>0) ![UnaryTemplate.tape n,UWalkUnary.source R n,List.replicate R false] := by
  have hc:=(LiteralCacheAllocate.local_copy R n).pad (![0,0,R])
  have hi : (fun i=>ZeroPadding.pad ((![0,0,R] : Fin 3→Nat) i)
      ((![UnaryTemplate.tape n,List.replicate R false,[]] : Fin 3→List Bool) i))=
      ![UnaryTemplate.tape n,List.replicate R false,List.replicate R false] := by
    funext i;fin_cases i <;>simp [ZeroPadding.pad_zero,ZeroPadding.pad]
  have ho : (fun i=>ZeroPadding.pad ((![0,0,R] : Fin 3→Nat) i)
      ((![UnaryTemplate.tape n,UWalkUnary.source R n,List.replicate (n+2) false] : Fin 3→List Bool) i))=
      ![UnaryTemplate.tape n,UWalkUnary.source R n,List.replicate R false] := by
    funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact (Rewind.Workspace.pad_zeros R (n+2)).trans (congrArg (fun k=>List.replicate k false) (max_eq_left h))
  exact (hc.congr_in rfl hi).congr rfl ho

theorem step1 (R tag count : Nat) (b : Fin 68→List Bool) :
    Step phase1 1 heads (input R tag count b) resetHeads (input R tag count b) := by
  have small:=PhysicalDriverMoves.run HeadMove.left (fun _ : Fin 2=>1)
    (fun i=>input R tag count b (moveSlots i))
  apply PhysicalFocusBoundary.focus small moveSlots (by decide)
    heads resetHeads (input R tag count b) (input R tag count b)
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i hi
    have h1 : i≠1 := fun h=>hi 0 h.symm
    have h61 : i≠61 := fun h=>hi 1 h.symm
    exact ⟨by simp [heads,LiteralCacheAllocate.heads,resetHeads,h1,h61],rfl⟩

theorem scratch_away (i : Fin 63) : scratchSlots i≠59 ∧ scratchSlots i≠60 ∧
    scratchSlots i≠62 ∧ scratchSlots i≠64 ∧ scratchSlots i≠65 := by
  fin_cases i <;>decide

theorem step2 (R tag count : Nat) (b : Fin 68→List Bool)
    (hb : ∀ i,i≠59→i≠60→i≠62→i≠64→i≠65→(b i).length≤R) :
    Step phase2 (2*R+4) resetHeads (input R tag count b) resetHeads (cleared R tag count) := by
  have bound (j : Fin 63) : (input R tag count b (scratchSlots j)).length≤R := by
    obtain ⟨h59,h60,h62,h64,h65⟩:=scratch_away j
    simpa only [input,if_neg h59,if_neg h60,if_neg h62,if_neg h64,if_neg h65]
      using hb _ h59 h60 h62 h64 h65
  have small:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3)
    (fun j=>input R tag count b (scratchSlots j)) bound)
  rw [Nat.max_eq_left (by omega : R+1≤R+3)] at small
  apply PhysicalFocusBoundary.focus small clearSlots (by decide)
    resetHeads resetHeads (input R tag count b) (cleared R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi
    by_cases h62 : i=62
    · subst i;exact ⟨rfl,rfl⟩
    by_cases h64 : i=64
    · subst i;exact ⟨rfl,rfl⟩
    by_cases h65 : i=65
    · subst i;exact ⟨rfl,rfl⟩
    have hv62 : i.val≠62 := fun h=>h62 (Fin.ext h)
    have hv64 : i.val≠64 := fun h=>h64 (Fin.ext h)
    have hv65 : i.val≠65 := fun h=>h65 (Fin.ext h)
    have cases : i.val<59 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=63 ∨ i=66 ∨ i=67 := by
      simp only [Fin.ext_iff]
      omega
    rcases cases with h|h|h|h|h|h|h
    · let j : Fin 63:=⟨i.val,by omega⟩
      have he : clearSlots (j.castAdd 2)=i := by
        apply Fin.ext
        simp only [clearSlots,Fin.addCases_left,scratchSlots]
        simp [j,h]
      exact False.elim (hi _ he)
    · subst i;exact False.elim (hi 63 rfl)
    · subst i;exact False.elim (hi 64 rfl)
    · subst i;exact False.elim (hi 59 rfl)
    · subst i;exact False.elim (hi 60 rfl)
    · subst i;exact False.elim (hi 61 rfl)
    · subst i;exact False.elim (hi 62 rfl)

theorem step3 (R tag count : Nat) (h : tag+2≤R) :
    Step phase3 (2*tag+6) resetHeads (cleared R tag count) resetHeads (bank3 R tag count) := by
  have small:=local_copy R tag h
  apply PhysicalFocusBoundary.focus small tagSlots (by decide)
    resetHeads resetHeads (cleared R tag count) (bank3 R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi
    fin_cases i <;>simp [tagSlots,Fin.forall_fin_succ] at hi
    all_goals exact ⟨rfl,rfl⟩

theorem step4 (R tag count : Nat) (h : count+2≤R) :
    Step phase4 (2*count+6) resetHeads (bank3 R tag count) resetHeads (bank4 R tag count) := by
  have small:=local_copy R count h
  apply PhysicalFocusBoundary.focus small indexSlots (by decide)
    resetHeads resetHeads (bank3 R tag count) (bank4 R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi
    fin_cases i <;>simp [indexSlots,Fin.forall_fin_succ] at hi
    all_goals exact ⟨rfl,rfl⟩

theorem step5 (R tag count : Nat) (h : count+2≤R) :
    Step phase5 (2*count+6) resetHeads (bank4 R tag count) resetHeads (ready R tag count) := by
  have small:=local_copy R count h
  apply PhysicalFocusBoundary.focus small driverSlots (by decide)
    resetHeads resetHeads (bank4 R tag count) (ready R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i hi
    fin_cases i <;>simp [driverSlots,Fin.forall_fin_succ] at hi
    all_goals exact ⟨rfl,rfl⟩

theorem step6 (R tag count : Nat) : Step phase6 1 resetHeads (ready R tag count) heads (ready R tag count) := by
  have small:=PhysicalDriverMoves.run HeadMove.right (fun _ : Fin 2=>0)
    (fun i=>ready R tag count (moveSlots i))
  apply PhysicalFocusBoundary.focus small moveSlots (by decide)
    resetHeads heads (ready R tag count) (ready R tag count)
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i;fin_cases i <;>rfl
  · intro i;rfl
  · intro i hi
    have h1 : i≠1 := fun h=>hi 0 h.symm
    have h61 : i≠61 := fun h=>hi 1 h.symm
    exact ⟨by simp [heads,LiteralCacheAllocate.heads,resetHeads,h1,h61],rfl⟩

theorem run (R tag count : Nat) (b : Fin 68→List Bool)
    (ht : tag+2≤R) (hc : count+2≤R)
    (hb : ∀ i,i≠59→i≠60→i≠62→i≠64→i≠65→(b i).length≤R) :
    Step machine (budget R tag count) heads (input R tag count b) heads (ready R tag count) := by
  have result:=(((((step1 R tag count b).seq (step2 R tag count b hb)).seq
    (step3 R tag count ht)).seq (step4 R tag count hc)).seq (step5 R tag count hc)).seq (step6 R tag count)
  convert result using 1 <;>first | rfl | (unfold budget;omega)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheReload
