import Proof.CaseAnalysis.RowsCountBinary
import Proof.Packets.VectorCounter
import Proof.Rows.SourceDockCore

/-! Actual logarithmic digit-width generation from the runtime unary count.
The count is first encoded, its binary length is scanned, and the floor log is
incremented. Zero follows the same physical program and produces width one. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.SourceDigitWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer

def logSlots : Fin 3→Fin 12:=![5,10,11]
def outSlot : Fin 1→Fin 12:=fun _=>10
theorem log_inj : Function.Injective logSlots:=by decide
theorem out_inj : Function.Injective outSlot:=by decide
noncomputable def countMachine:=TapeEmbedding.machine 2 CloseoutRowsCountBinary.machine
noncomputable def logMachine:=RecoveryFocus.machine logSlots ClockFloorLog.machine
noncomputable def bumpMachine:=RecoveryFocus.machine outSlot VectorCounter.increment
noncomputable def moveMachine:=RecoveryFocus.machine outSlot (PhysicalDriverMoves.machine 1 .left)
noncomputable def machine:=Composition.machine (Composition.machine
  (Composition.machine countMachine logMachine) bumpMachine) moveMachine

def input (M : Nat) : Fin 12→List Bool:=fun i=>if i=0 then List.replicate M true else []
def digitWidth (M : Nat):=Nat.log 2 M+1
def budget (M : Nat):=((CloseoutRowsCountBinary.budget M+1+
  (4*(CloseoutRowsCountBinary.bits M).length+8))+1+(2*Nat.log 2 M+2))+1+1

theorem log_length (M : Nat) : (CloseoutRowsCountBinary.bits M).length-1=Nat.log 2 M:=by
  by_cases hm:M=0
  · subst M;simp [CloseoutRowsCountBinary.bits]
  · simp [CloseoutRowsCountBinary.bits,hm,SignedSortKey.binary_length,natBitLength]

 theorem run (M : Nat) : ∃ O,
    Step machine (budget M) (fun _=>0) (input M) (fun _=>0) O ∧
      O 10=CompareMachine.word (digitWidth M) ∧
      O 1=List.replicate M true ∧ O 3=UnaryTemplate.tape M ∧
      O 5=frame (CloseoutRowsCountBinary.bits M) := by
  obtain ⟨C,⟨cr,cRun,cTapes,cHeads,cSteps⟩,c1,c3,c5⟩:=CloseoutRowsCountBinary.count_run M
  have cStep:Step CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.budget M)
      (fun _=>0) (CloseoutRowsCountBinary.input M) (fun _=>0) C:=
    ⟨cr,cRun,funext cHeads,cTapes,cSteps⟩
  have c:=cStep.embed (fun _ : Fin 2=>0) (fun _=>[])
  have cIn:Fin.addCases (m:=10) (n:=2) (CloseoutRowsCountBinary.input M) (fun _=>[])=input M:=by
    funext i;fin_cases i <;>rfl
  have z:(Fin.addCases (m:=10) (n:=2) (fun _=>0) (fun _=>0):Fin 12→Nat)=(fun _=>0):=by
    funext i;fin_cases i <;>rfl
  rw [cIn,z] at c
  let A:Fin 12→List Bool:=Fin.addCases (m:=10) (n:=2) C (fun _=>[])
  obtain ⟨lr,lRun,l0,l1,_l2,lHeads,lSteps⟩:=ClockFloorLog.entry_run (CloseoutRowsCountBinary.bits M)
  have lStep:Step ClockFloorLog.machine (4*(CloseoutRowsCountBinary.bits M).length+8)
      (fun _=>0) (ClockFloorLog.input (CloseoutRowsCountBinary.bits M)) lr.final.heads lr.final.tapes:=
    ⟨lr,lRun,rfl,rfl,lSteps.le⟩
  have l:=SourceDock.dock lStep logSlots log_inj (fun _=>0) A (by intro j;rfl) (by
    intro j;fin_cases j
    · exact c5
    · rfl
    · rfl)
  let LH:=dockH logSlots (fun _=>0) lr.final.heads
  let LA:=install logSlots A lr.final.tapes
  have lh:LH 10=1:=(dockH_slot logSlots log_inj (fun _=>0) lr.final.heads 1).trans
    (by rw [lHeads];rfl)
  have lw:LA 10=CompareMachine.word (Nat.log 2 M):=
    (install_slot logSlots log_inj A lr.final.tapes 1).trans (by rw [l1,log_length])
  have b:=SourceDock.dock (VectorCounter.increment_run (Nat.log 2 M)) outSlot out_inj LH LA
    (by intro j;exact lh) (by intro j;exact lw)
  let BH:=dockH outSlot LH (fun _=>1)
  let BA:=install outSlot LA (fun _=>CompareMachine.word (digitWidth M))
  have bh:BH 10=1:=dockH_slot outSlot out_inj LH (fun _=>1) 0
  have v:=SourceDock.dock (PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>BA 10)) outSlot out_inj BH BA (by intro j;exact bh) (by intro j;rfl)
  have all:=((c.seq l).seq b).seq v
  have words:install outSlot BA (fun _=>BA 10)=BA:=install_existing outSlot BA _ (by intro j;rfl)
  have heads:dockH outSlot BH (fun _=>HeadMove.left.apply 1)=(fun _=>0):=by
    funext i
    by_cases hi:i=10
    · subst i
      exact dockH_slot outSlot out_inj BH (fun _=>HeadMove.left.apply 1) 0
    · have outside:∀j,outSlot j≠i:=by intro j he;exact hi he.symm
      rw [dockH_other outSlot _ _ _ outside]
      dsimp only [BH]
      rw [dockH_other outSlot _ _ _ outside]
      by_cases h5:i=5
      · subst i
        exact (dockH_slot logSlots log_inj (fun _=>0) lr.final.heads 0).trans (by rw [lHeads];rfl)
      · by_cases h11:i=11
        · subst i
          exact (dockH_slot logSlots log_inj (fun _=>0) lr.final.heads 2).trans (by rw [lHeads];rfl)
        · apply dockH_other logSlots (fun _=>0) lr.final.heads i
          intro j he
          fin_cases j
          · exact h5 he.symm
          · exact hi he.symm
          · exact h11 he.symm
  refine ⟨BA,?_,?_,?_,?_,?_⟩
  · change Step machine (budget M) (fun _=>0) (input M)
      (dockH outSlot BH (fun _=>HeadMove.left.apply 1))
      (install outSlot BA (fun _=>BA 10)) at all
    rw [words,heads] at all
    exact all
  · exact install_slot outSlot out_inj LA _ 0
  · dsimp only [BA]
    rw [install_other outSlot _ _ _ (by decide)]
    dsimp only [LA]
    rw [install_other logSlots _ _ _ (by decide)]
    exact c1
  · dsimp only [BA]
    rw [install_other outSlot _ _ _ (by decide)]
    dsimp only [LA]
    rw [install_other logSlots _ _ _ (by decide)]
    exact c3
  · dsimp only [BA]
    rw [install_other outSlot _ _ _ (by decide)]
    exact (install_slot logSlots log_inj A lr.final.tapes 0).trans l0

end Completion.SourceDigitWidth
