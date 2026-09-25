import Proof.Packets.PacketsXWalkLiteralProducedReserveRetained
import Proof.Packets.PacketsXWalkLiteralProducedReserveFrame
import Proof.Packets.PacketsXMajorityCompleteColdRun
import Proof.Packets.WalkTranscriptColumnController

/-! Fixed physical alignment of the produced walk, scalar metadata and
column-majority controller. Every added tape is initially empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

/-- The sample driver is the scalar producer's actual Compare(n+1) output. -/
def coldView (i : Fin 333) : Fin 742 :=
  if i=332 then 709 else (WalkLiteralProduced.coldSlots i).castAdd 309

def controllerSlots : Fin 472→Fin 742 :=
  Fin.addCases (m:=333) (n:=139) (motive:=fun _=>Fin 742) coldView
    (fun i=>⟨566+i.val,by have hb:=i.isLt;omega⟩)
def workerSlots (i : Fin 471) := controllerSlots (WalkTranscriptColumnController.slots (i.castAdd 1))
def majoritySlots (j : Fin 137) : Fin 742 :=
  if j=44 then 566 else if j.val<44 then ⟨568+j.val,by omega⟩ else ⟨567+j.val,by have hb:=j.isLt;omega⟩
def metadataSlots : Fin 5→Fin 742 := ![81,82,71,41,427]
def coldSlots : Fin 178→Fin 742 :=
  Fin.addCases (m:=137) (n:=41) (motive:=fun _=>Fin 742) majoritySlots
    (Fin.addCases (m:=5) (n:=36) (motive:=fun _=>Fin 742) metadataSlots
      (fun i=>⟨705+i.val,by have hb:=i.isLt;omega⟩))
def columnSlots : Fin 9→Fin 742 := ![156,426,382,388,422,386,566,709,567]
def zeroSlots : Fin 3→Fin 742 := ![567,424,741]
def raiseSlots : Fin 3→Fin 742 := ![388,709,567]

theorem cold_view_range (i : Fin 333) : (coldView i).val<428 ∨ coldView i=709 := by
  by_cases hi:i=332
  · simp only [coldView,if_pos hi];exact Or.inr trivial
  · simp only [coldView,if_neg hi]
    exact Or.inl (WalkLiteralProduced.cold_lt i)

theorem cold_view_injective : Function.Injective coldView := by
  intro i j he
  by_cases hi:i=332
  · subst i
    by_cases hj:j=332
    · exact hj.symm
    · have hb:=WalkLiteralProduced.cold_lt j
      have hv:=congrArg Fin.val he
      simp only [coldView,if_pos rfl,if_neg hj,Fin.val_castAdd] at hv
      change 709=(WalkLiteralProduced.coldSlots j).val at hv
      omega
  by_cases hj:j=332
  · subst j
    have hb:=WalkLiteralProduced.cold_lt i
    have hv:=congrArg Fin.val he
    simp only [coldView,if_pos rfl,if_neg hi,Fin.val_castAdd] at hv
    change (WalkLiteralProduced.coldSlots i).val=709 at hv
    omega
  · simp only [coldView,if_neg hi,if_neg hj] at he
    exact WalkLiteralProduced.cold_slots_injective (Fin.castAdd_inj.mp he)

theorem controller_injective : Function.Injective controllerSlots := by
  intro i j
  refine Fin.addCases (m:=333) (n:=139) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=333) (n:=139) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [controllerSlots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 333=>k.castAdd 139) (cold_view_injective he)
  · intro he
    have hb:=b.isLt
    have hv:=congrArg Fin.val he
    simp only [controllerSlots,Fin.addCases_left,Fin.addCases_right] at hv
    rcases cold_view_range a with ha|ha
    · omega
    · rw [ha] at hv;omega
  · intro he
    have ha:=a.isLt
    have hv:=congrArg Fin.val he
    simp only [controllerSlots,Fin.addCases_left,Fin.addCases_right] at hv
    rcases cold_view_range b with hb|hb
    · omega
    · rw [hb] at hv;omega
  · intro he
    apply Fin.ext
    have hv:=congrArg Fin.val he
    simp only [controllerSlots,Fin.addCases_right] at hv
    dsimp at hv ⊢
    omega

theorem worker_injective : Function.Injective workerSlots := by
  intro i j he
  apply Fin.castAdd_inj.mp
  exact WalkTranscriptColumnController.slots_injective (controller_injective he)

theorem majority_worker : ∀j,majoritySlots j=workerSlots (WalkTranscriptColumnArena.majoritySlots j) := by decide

theorem majority_injective : Function.Injective majoritySlots := by
  intro i j he
  rw [majority_worker,majority_worker] at he
  exact WalkTranscriptColumnArena.majority_injective (worker_injective he)

theorem majority_range (i : Fin 137) : 566≤(majoritySlots i).val ∧ (majoritySlots i).val<704 := by
  have hb:=i.isLt
  unfold majoritySlots
  split_ifs <;>dsimp <;>omega

theorem metadata_range (i : Fin 5) : (metadataSlots i).val<428 := by fin_cases i <;>decide

theorem cold_injective : Function.Injective coldSlots := by
  intro i j
  refine Fin.addCases (m:=137) (n:=41) (fun a=>?_) (fun a=>?_) i <;>
    refine Fin.addCases (m:=137) (n:=41) (fun b=>?_) (fun b=>?_) j
  · intro he
    simp only [coldSlots,Fin.addCases_left] at he
    exact congrArg (fun k : Fin 137=>k.castAdd 41) (majority_injective he)
  · refine Fin.addCases (m:=5) (n:=36) (fun b=>?_) (fun b=>?_) b
    · intro he
      have ha:=majority_range a;have hb:=metadata_range b
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
    · intro he
      have ha:=majority_range a
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
  · refine Fin.addCases (m:=5) (n:=36) (fun a=>?_) (fun a=>?_) a
    · intro he
      have ha:=metadata_range a;have hb:=majority_range b
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
    · intro he
      have hb:=majority_range b
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
  · refine Fin.addCases (m:=5) (n:=36) (fun a=>?_) (fun a=>?_) a <;>
      refine Fin.addCases (m:=5) (n:=36) (fun b=>?_) (fun b=>?_) b
    · intro he
      simp only [coldSlots,Fin.addCases_right,Fin.addCases_left] at he
      have inj : Function.Injective metadataSlots := by decide
      exact congrArg (fun k : Fin 5=>(k.castAdd 36).natAdd 137) (inj he)
    · intro he
      have ha:=metadata_range a
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
    · intro he
      have hb:=metadata_range b
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_left,Fin.addCases_right] at hv
      omega
    · intro he
      apply Fin.ext
      have hv:=congrArg Fin.val he
      simp only [coldSlots,Fin.addCases_right] at hv
      dsimp at hv ⊢;omega

theorem column_worker : ∀j,columnSlots j=workerSlots (WalkTranscriptColumnArena.columnSlots j) := by decide
theorem column_injective : Function.Injective columnSlots := by decide

def zeroSelect : Fin 1→Option (Fin 0) := fun _=>none
def zeroMachine := RecoveryFocus.machine zeroSlots (NativeFanout.machine zeroSelect)
def raise := RecoveryFocus.machine raiseSlots (PhysicalDriverMoves.machine 3 .right)
def lowerTime := PhysicalIndexReload.move (709 : Fin 742) .left
def raiseTime := PhysicalIndexReload.move (709 : Fin 742) .right
def scalarFront := RecoveryFocus.machine coldSlots
  (Composition.machine MajorityComplete.Cold.lower MajorityComplete.Cold.scalar)
def majorityFinish := RecoveryFocus.machine coldSlots
  (Composition.machine MajorityComplete.Cold.square
    (Composition.machine MajorityComplete.Cold.copy MajorityComplete.Cold.initializeMachine))
def extract := RecoveryFocus.machine columnSlots TranscriptColumn.program

end
end Theorem25Completion.WalkLiteralProducedMajority
