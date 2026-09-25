import Proof.Rows.CircuitPowerInput

/-! A complete reusable selected coefficient call from the actual outer TOP
frame and one private binary digit, with paid extraction and payload cleanup. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
open PCJ45bee56da9f34d5a_CircuitPowerInput
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerReady.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitPowerInput.extract
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitPowerInput.evaluate
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitPowerInput.wipe

def budget {n :Nat} (words :List (List Bool)) (circuit :Fin words.length) (C :Nat)
 (gs :List (ExactThresholdGate n)) (i :Fin gs.length) (w F U v :Nat):=
 (PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit C+4*U+12)+1+
 PCJ45bee56da9f34d5a_SelectedPowerReady.budget gs i w F U v+1+(2*U+4)

theorem run (words :List (List Bool)) (circuit :Fin words.length) (C :Nat)
 {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length)
 (a B p w F U v :Nat) (out :List Bool)
 (hb : ∀x∈words,x.length≤C) (htop : PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit C+2≤U)
 (hselected : words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
 (hu : PCPPQueryNatural.budget n<U) (hi : i.val<2^v) (hindex : MatrixUnaryTemplate.budget v i.val<U)
 (hpay : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
 (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
 (hg : (exactWord (gs.get i)).length+2≤U)
 (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hB : B<2^w)
 (hw : ∀j,C10NativeResidueCallback.coreBudget false ((gs.get i).weight j) w+1≤F)
 (ht : C10NativeResidueCallback.coreBudget true (gs.get i).target w+1≤F)
 (hU : 1024*(w+1)^2+2≤U) :
 Step machine (budget words circuit C gs i w F U v)
  (heads out.length) (bank a B p w F U v i.val circuit.val (words.flatMap frame) [] out)
  (heads (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length)
  (bank ((a*B)%p) B p w F U v i.val circuit.val (words.flatMap frame) []
   (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))) :=by
 have first:=extract_run words circuit C a B p w F U v i.val out hb htop
 rw [hselected] at first
 have middle0:=((PCJ45bee56da9f34d5a_SelectedPowerReady.run gs i a B p w F U v out hu hi hindex hpay hf hg hp hpw ha hB hw ht hU).pad (caps U)).embed
  (![0,1] :Fin 2→Nat) (![frame (words.flatMap frame),ZeroPadding.pad U (CompareMachine.word circuit.val)] :Fin 2→List Bool)
 have middle:Step evaluate (PCJ45bee56da9f34d5a_SelectedPowerReady.budget gs i w F U v)
  (heads out.length) (bank a B p w F U v i.val circuit.val (words.flatMap frame) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out)
  (heads (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length)
  (bank ((a*B)%p) B p w F U v i.val circuit.val (words.flatMap frame) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
   (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))):=by
   unfold evaluate
   exact (middle0.congr_in rfl rfl).congr rfl rfl
 have last:=wipe_run ((a*B)%p) B p w F U v i.val circuit.val (words.flatMap frame)
  (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
  (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))) hpay
 exact (first.seq middle).seq last
end
end PCJ45bee56da9f34d5a_CircuitPowerRun
