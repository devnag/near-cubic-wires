import Proof.Packets.PacketsXCycleTableDriver

/-! A paid table-enumeration seed from one actual raw residual width. Both
the framed binary zero assignment and the full unary repetition driver are
constructed by fixed machines; no enumerator counter word is supplied. -/
namespace Theorem25Completion.CycleTableSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots : Fin 17→Fin 21:=![0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
def input (s : Nat) : Fin 21→List Bool:=
  Fin.addCases (m:=5) (n:=16) (motive:=fun _=>List Bool) (ClockScalarFields.zeroInput s) (fun _=>[])
def heads (i : Fin 21) : Nat:=if i=19 then 1 else 0
abbrev machine:=Composition.machine (TapeEmbedding.machine 16 ClockNormalize.machine)
  (RecoveryFocus.machine slots CycleTableDriver.machine)
def budget (s : Nat):=4*s+5+CycleTableDriver.budget s

theorem run (s : Nat) : ∃ out,
    Step machine (budget s) (fun _=>0) (input s) heads out ∧
      out 2=frame (SignedSortKey.binary s 0) ∧ out 4=List.replicate (2*s+1) false ∧
      out 19=CompareMachine.word (2^s-1) ∧ out 17=UnaryTemplate.tape (2^s) := by
  obtain ⟨z,hz,hz0,_,hz2,_,hz4,hzh,hzs⟩:=ClockScalarFields.zero_run s
  have zero:Step ClockNormalize.machine (4*s+4) (fun _=>0)
      (ClockScalarFields.zeroInput s) (fun _=>0) z.final.tapes:=
    ⟨z,hz,funext hzh,rfl,hzs.le⟩
  let middle:=Fin.addCases (m:=5) (n:=16) (motive:=fun _=>List Bool) z.final.tapes (fun _=>[])
  have first:=zero.embed (fun _ : Fin 16=>0) (fun _ : Fin 16=>[])
  obtain ⟨p,hp,hp15,hp13⟩:=CycleTableDriver.run s
  have second:=hp.dock slots (by decide) (fun _ : Fin 21=>0) middle
    (by intro j;fin_cases j <;>rfl) (by
      intro j;fin_cases j
      · exact hz0
      all_goals rfl)
  have hh:dockH slots (fun _ : Fin 21=>0) CycleTableDriver.heads=heads := by
    funext i
    by_cases he:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=he
      rw [dockH_slot slots (by decide)]
      fin_cases j <;>rfl
    · have away:∀j,slots j≠i:=by simpa only [not_exists] using he
      rw [dockH_other slots _ _ i away]
      have hn:i≠19:=Ne.symm (away 15)
      simp [heads,hn]
  have hzheads : Fin.addCases (m:=5) (n:=16) (motive:=fun _=>Nat)
      (fun _=>0) (fun _=>0)=(fun _ : Fin 21=>0) := by
    funext i;fin_cases i <;>rfl
  have first' : Step (TapeEmbedding.machine 16 ClockNormalize.machine) (4*s+4)
      (fun _=>0) (input s) (fun _=>0) middle :=
    (first.congr_in hzheads rfl).congr hzheads rfl
  have combined:=first'.seq second
  have cost:4*s+4+1+CycleTableDriver.budget s=budget s:=by unfold budget;omega
  rw [cost] at combined
  have step:Step machine (budget s) (fun _=>0) (input s) heads (install slots middle p):=
    combined.congr hh rfl
  refine ⟨_,step,?_,?_,?_,?_⟩
  · exact (install_other slots _ _ 2 (by decide)).trans hz2
  · exact (install_other slots _ _ 4 (by decide)).trans hz4
  · exact (install_slot slots (by decide) _ _ 15).trans hp15
  · exact (install_slot slots (by decide) _ _ 13).trans hp13

end
end Theorem25Completion.CycleTableSeed
