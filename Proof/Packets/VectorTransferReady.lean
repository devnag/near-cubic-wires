import Proof.Packets.VectorTransferLoop

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (sourcePos targetPos : Nat) : Fin 6→Nat := ![1,sourcePos,targetPos,0,0,1]
def tapes (R N : Nat) (source target : List Bool) : Fin 6→List Bool :=
  ![UnaryTemplate.tape R,source,target,List.replicate R false,[],CompareMachine.word N]
def backSourceSlots : Fin 4→Fin 6 := ![0,1,4,5]
def backTargetSlots : Fin 4→Fin 6 := ![0,2,4,5]
def backSource := RecoveryFocus.machine backSourceSlots MaskBack.machine
def backTarget := RecoveryFocus.machine backTargetSlots MaskBack.machine
def machine := Composition.machine loop (Composition.machine backSource
  (Composition.machine backSource (Composition.machine backTarget backTarget)))
def budget (R N : Nat) := N*(24*R+46)+19

theorem backSource_run (R N pos tpos : Nat) (source target : List Bool) :
    Step backSource (N*(2*R+5)+3) (heads (pos+N*R) tpos) (tapes R N source target)
      (heads pos tpos) (tapes R N source target) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run R N pos source []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h backSourceSlots (by decide)
    (heads (pos+N*R) tpos) (heads pos tpos) (tapes R N source target) (tapes R N source target)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem backTarget_run (R N spos pos : Nat) (source target : List Bool) :
    Step backTarget (N*(2*R+5)+3) (heads spos (pos+N*R)) (tapes R N source target)
      (heads spos pos) (tapes R N source target) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run R N pos target []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h backTargetSlots (by decide)
    (heads spos (pos+N*R)) (heads spos pos) (tapes R N source target) (tapes R N source target)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem loop_step (R : Nat) (rows : List Pair) (spre spost tpre tpost : List Bool)
    (hf : Fits R rows) :
    Step loop (rows.length*(16*R+26)+3) (heads spre.length tpre.length)
      (tapes R rows.length (spre++sourceBytes rows++spost) (tpre++targetBytes rows++tpost))
      (heads (spre.length+rows.length*(2*R)) (tpre.length+rows.length*(2*R)))
      (tapes R rows.length (spre++List.replicate (rows.length*(2*R)) false++spost)
        (tpre++sourceBytes rows++tpost)) := by
  obtain ⟨r,rr,rf,_⟩:=loop_run R rows spre spost tpre tpost hf
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  convert h using 1
  all_goals funext i;fin_cases i <;> rfl

theorem run (R : Nat) (rows : List Pair) (spre spost tpre tpost : List Bool)
    (hf : Fits R rows) :
    Step machine (budget R rows.length) (heads spre.length tpre.length)
      (tapes R rows.length (spre++sourceBytes rows++spost) (tpre++targetBytes rows++tpost))
      (heads spre.length tpre.length)
      (tapes R rows.length (spre++List.replicate (rows.length*(2*R)) false++spost)
        (tpre++sourceBytes rows++tpost)) := by
  let source:=spre++List.replicate (rows.length*(2*R)) false++spost
  let target:=tpre++sourceBytes rows++tpost
  have first:=loop_step R rows spre spost tpre tpost hf
  have second:=backSource_run R rows.length (spre.length+rows.length*R)
    (tpre.length+rows.length*(2*R)) source target
  have third:=backSource_run R rows.length spre.length
    (tpre.length+rows.length*(2*R)) source target
  have fourth:=backTarget_run R rows.length spre.length (tpre.length+rows.length*R) source target
  have fifth:=backTarget_run R rows.length spre.length tpre.length source target
  have eqn (n : Nat) : n+rows.length*R+rows.length*R=n+rows.length*(2*R) := by ring
  rw [eqn] at second fourth
  have h:=first.seq (second.seq (third.seq (fourth.seq fifth)))
  have fuel : (rows.length*(16*R+26)+3)+1+((rows.length*(2*R+5)+3)+1+
      ((rows.length*(2*R+5)+3)+1+((rows.length*(2*R+5)+3)+1+(rows.length*(2*R+5)+3))))=
      budget R rows.length := by unfold budget;ring
  rw [fuel] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTransfer
