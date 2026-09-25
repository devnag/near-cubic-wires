import Proof.Packets.PacketsXWalkLiteralProducedMajorityFront
import Proof.Packets.PacketsXMajorityCompleteScalarFrame

/-! Paid first-column extraction between the scalar and arithmetic stages. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProducedMajority
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

def columnStartHeads : Fin 9→Nat := ![1,0,0,0,1,0,0,0,0]
def raisedHeads (H : Fin 742→Nat) := dockH raiseSlots H (fun _=>1)
def loweredHeads (H : Fin 742→Nat) := Function.update (raisedHeads H) 709 0

theorem raise_run (H : Fin 742→Nat) (A : Fin 742→List Bool)
    (hh : ∀i,H (columnSlots i)=columnStartHeads i) : Step raise 1 H A (raisedHeads H) A := by
  have hp : ∀i,H (raiseSlots i)=0 := by
    intro i;fin_cases i
    · exact hh 3
    · exact hh 7
    · exact hh 8
  have h:=SourceDock.dock (PhysicalDriverMoves.run .right (fun _ : Fin 3=>0) (fun i=>A (raiseSlots i)))
    raiseSlots (by decide) H A hp (by intro i;rfl)
  exact h.congr rfl (install_existing raiseSlots A _ (by intro i;rfl))

theorem raised_column (H : Fin 742→Nat) (hh : ∀i,H (columnSlots i)=columnStartHeads i) :
    ∀i,raisedHeads H (columnSlots i)=TranscriptColumn.heads 0 0 i := by
  intro i;fin_cases i
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 0
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 1
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 2
  · change dockH raiseSlots H (fun _=>1) (raiseSlots 0)=_
    rw [dockH_slot raiseSlots (by decide)];rfl
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 4
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 5
  · rw [raisedHeads,dockH_other _ _ _ _ (by decide)];exact hh 6
  · change dockH raiseSlots H (fun _=>1) (raiseSlots 1)=_
    rw [dockH_slot raiseSlots (by decide)];rfl
  · change dockH raiseSlots H (fun _=>1) (raiseSlots 2)=_
    rw [dockH_slot raiseSlots (by decide)];rfl

def firstColumn := Composition.machine raise extract

theorem first_column_run (R N T S : Nat) (rows : Nat→List PacketVector.Packet)
    (hlen : ∀i,(rows i).length=N) (column : Fin N)
    (hfit : ∀i,∀P∈rows i,PacketVector.Fits R P) (hold : PacketVector.Fits R [])
    (H : Fin 742→Nat) (A : Fin 742→List Bool)
    (hh : ∀i,H (columnSlots i)=columnStartHeads i)
    (ha : ∀i,A (columnSlots i)=TranscriptColumn.residentTapes R N T column.val S
      (PacketTranscript.prefixBank R rows T) (PacketVector.payload R []) (PacketVector.count R []) [] i) :
    Step firstColumn (2+TranscriptColumn.budget R N T column.val) H A (raisedHeads H)
      (install columnSlots A (TranscriptColumn.residentTapes R N T column.val S
        (PacketTranscript.prefixBank R rows T)
        (PacketVector.payload R (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows hlen column) [] T))
        (PacketVector.count R (TranscriptColumn.previous (TranscriptColumn.rowPacket N rows hlen column) [] T))
        (PacketVector.bank R (List.ofFn (fun i : Fin T=>TranscriptColumn.rowPacket N rows hlen column i.val))))) := by
  have first:=raise_run H A hh
  have localRun:=TranscriptColumn.run_resident R N T S rows hlen column [] [] hfit hold
  have last:=SourceDock.dock localRun columnSlots column_injective (raisedHeads H) A
    (raised_column H hh) ha
  have last':=last.congr (SourceDock.heads_existing columnSlots _ _ (raised_column H hh)) rfl
  simpa only [firstColumn,extract,List.length_nil,List.nil_append] using first.seq last'

theorem column_cold_view (C R n : Nat) (A : Fin 742→List Bool) (col : Fin 9→List Bool) (bank : List Bool)
    (ha : ∀j,A (coldSlots j)=MajorityComplete.Cold.afterScalar C R n [] j)
    (hb : col 6=bank) (ht : col 7=CompareMachine.word (n+1)) :
    ∀j,install columnSlots A col (coldSlots j)=MajorityComplete.Cold.afterScalar C R n bank j := by
  intro j
  by_cases h44:j=44
  · subst j
    change install columnSlots A col (columnSlots 6)=_
    rw [install_slot columnSlots column_injective,hb,MajorityComplete.Cold.afterScalar]
    rw [install_other _ _ _ _ (by decide)]
    rfl
  by_cases h146:j=146
  · subst j
    change install columnSlots A col (columnSlots 7)=_
    rw [install_slot columnSlots column_injective,ht,MajorityComplete.Cold.afterScalar_count]
  · have away : ∀i,columnSlots i≠coldSlots j := by
      intro i he
      rcases column_cold_overlap i j he with hh|hh
      · exact h44 hh.2
      · exact h146 hh.2
    rw [install_other _ _ _ _ away,ha]
    have h:=congrFun (cold_scalar_update C R n [] bank) j
    simpa only [Function.update_of_ne h44] using h

theorem lowered_cold (H : Fin 742→Nat) (hh : ∀j,H (coldSlots j)=0) :
    ∀j,loweredHeads H (coldSlots j)=0 := by
  intro j
  by_cases hj:j=146
  · subst j;exact Function.update_self _ _ _
  · have different : coldSlots j≠709 := by
      intro he
      apply hj
      exact cold_injective he
    have away : ∀i,raiseSlots i≠coldSlots j := by
      have overlap : ∀i j,raiseSlots i=coldSlots j→j=146 := by decide
      intro i he
      exact hj (overlap i j he)
    rw [loweredHeads,Function.update_of_ne different,raisedHeads,dockH_other _ _ _ _ away]
    exact hh j

theorem lower_time_run (H : Fin 742→Nat) (A : Fin 742→List Bool) :
    Step lowerTime 1 (raisedHeads H) A (loweredHeads H) A := by
  have hp : raisedHeads H 709=1 := dockH_slot raiseSlots (by decide) H (fun _=>1) 1
  have h:=PhysicalIndexReload.move_run (709 : Fin 742) .left (raisedHeads H) A
  simpa only [hp,HeadMove.apply,lowerTime,loweredHeads] using h

end
end Theorem25Completion.WalkLiteralProducedMajority
