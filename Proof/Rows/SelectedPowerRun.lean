import Proof.Rows.SelectedPowerBody

/-! Actual selected TOP child to its scaled coefficient block, then factor
update and full native-buffer reuse. No selected coefficient stream is assumed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_SelectedPowerBank
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerBank.locate
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerBody.emit
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerBody.clear

def machine:=Composition.machine
 (Composition.machine PCJ45bee56da9f34d5a_SelectedPowerBank.locate PCJ45bee56da9f34d5a_SelectedPowerBody.emit)
 PCJ45bee56da9f34d5a_SelectedPowerBody.clear

def budget {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w F U : Nat) :=
 (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13)+1+
 (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U (gs.get i).target+1+(1024*(w+1)^2+10*U+18*w+45))+1+(4*U+9)

theorem run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length)
 (a B p w F U : Nat) (out : List Bool)
 (hn : n+2≤U) (hpay : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
 (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
 (hg : (exactWord (gs.get i)).length+2≤U)
 (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hB : B<2^w)
 (hw : ∀j,C10NativeResidueCallback.coreBudget false ((gs.get i).weight j) w+1≤F)
 (ht : C10NativeResidueCallback.coreBudget true (gs.get i).target w+1≤F)
 (hU : 1024*(w+1)^2+2≤U) :
 Step machine (budget gs i w F U)
  (heads 0 out.length) (bank a B p w F U n i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) [] out)
  (heads 0 (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length)
  (bank ((a*B)%p) B p w F U n i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) []
    (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))) :=by
 have first:=PCJ45bee56da9f34d5a_SelectedPowerBank.locate_run gs i a B p w F U out hn hpay hf hg
 have middle:=PCJ45bee56da9f34d5a_SelectedPowerBody.emit_run (gs.get i) a B p w F U i.val
  (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out hp hpw ha hB hw ht hU
 have last:=PCJ45bee56da9f34d5a_SelectedPowerBody.clear_run ((a*B)%p) B p w F U n i.val
  (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) (exactWord (gs.get i))
  (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))) (by omega)
 simp only [List.length_append,PCJ45bee56da9f34d5a_PowerEquation.result_length] at last
 have h:=(first.seq middle).seq last
 simpa only [machine,budget,List.length_append,PCJ45bee56da9f34d5a_PowerEquation.result_length] using h
end
end PCJ45bee56da9f34d5a_SelectedPowerRun
