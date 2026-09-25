import Proof.MachineModel.BankZero
import Proof.CaseAnalysis.WitnessHeaderSwitch

/-! Inspect the existing raw stream marker without moving its cursor. Exactly
one existing incidence/bank worker runs, including the paid empty clear. -/
namespace NearCubicWires.ExtIncidence.BankBranch
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem stream_marker (ms : List (List ℕ)) (pre tail : List Bool) :
    readTapeBit (pre++stream ms++tail) pre.length=decide (0 < ms.length):=by
  cases ms with
  | nil=>simpa only [stream_nil,List.append_assoc,List.singleton_append,List.length_nil,
      Nat.lt_irrefl,decide_false] using
      Streaming.read_append pre tail false
  | cons m ms=>
    simpa only [stream_cons,monomialWord,List.cons_append,List.append_assoc,
      List.length_cons,Nat.zero_lt_succ,decide_true] using
      Streaming.read_append pre ((m.flatMap block++[false])++stream ms++tail) true

end
end NearCubicWires.ExtIncidence.BankBranch
