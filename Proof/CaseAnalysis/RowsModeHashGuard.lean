import Proof.CaseAnalysis.RowsModeHashReady
import Proof.CaseAnalysis.RowsModeHashCellMeaning

/-! A paid actual hash-cell scan returns the bitmap and original level
heads. Its three physical flags remain available to the literal Pair writer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashGuard
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsModeHashCell
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine:=MaskedReset.machine CloseoutRowsModeHashCell.machine (fun _=>true)
def data (level C : Nat) (bits : List Bool) (z s c : Bool) : Fin 6→List Bool:=
  Fin.addCases (m:=5) (n:=1) (motive:=fun _=>List Bool)
    (CloseoutRowsModeHashCell.data level bits z s c) (fun _=>List.replicate C false)

theorem ready (pre rest : List Bool) (C : Nat) (z s c : Bool) (hC : pre.length+2≤C) :
    Step machine (2*pre.length+6) (fun _=>0) (data pre.length C (pre++rest) z s c)
      (fun _=>0) (data pre.length C (pre++rest) (zeroFlag pre)
        (zeroFlag pre&&readTapeBit (pre++rest) pre.length)
        (zeroFlag pre&&!readTapeBit (pre++rest) pre.length)):=by
  obtain ⟨r,hr,rf,_⟩:=cell_run pre rest z s c
  have raw:=(Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).mask
    (fun _=>true) (by intro i hi;fin_cases i <;> rfl) hC
  have time:2*(pre.length+2)+2=2*pre.length+6:=by omega
  rw [time] at raw
  apply (raw.congr_in ?_ rfl).congr ?_ rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashGuard
