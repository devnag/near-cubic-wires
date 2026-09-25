import Proof.Rows.SelectedPowerPrepare

/-! Actual TOP arity and private binary digit feed the selected coefficient
mapper; both unary drivers are then paid back to their reusable cold bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
open PCJ45bee56da9f34d5a_SelectedPowerPrepare
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_SelectedPowerRun.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear

def emit:=TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_SelectedPowerRun.machine
def clearSlots:Fin 4→Fin 101:=![91,95,62,63]
def clear:=RecoveryFocus.machine clearSlots (PCJ45bee56da9f34d5a_HeaderRewind.clear 2)
def machine:=Composition.machine
 (Composition.machine (Composition.machine arity index) emit) clear

theorem heads_ready (len :Nat):
 Fin.addCases (m:=99) (n:=2) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_SelectedPowerBank.heads 0 len) (fun _=>0)=heads len 1 1 :=by
 funext i;fin_cases i <;>rfl

theorem clear_run (a B p w F U n key v :Nat) (source out :List Bool)
 (hn : n+2≤U) (hk : key+2≤U) :
 Step clear (4*U+9) (heads out.length 1 1) (bank a B p w F U n key v key source out)
  (heads out.length 0 0) (bank a B p w F U 0 0 v key source out) :=by
 let A :Fin 2→List Bool:=![ZeroPadding.pad U (CompareMachine.word n),ZeroPadding.pad U (UnaryTemplate.tape key)]
 have hA:∀i,(A i).length≤U:=by
  intro i;fin_cases i
  · change (ZeroPadding.pad U (CompareMachine.word n)).length≤U
    rw [ZeroPadding.pad_length]
    apply max_le (le_refl _)
    simp only [CompareMachine.word,List.length_cons,List.length_replicate];omega
  · change (ZeroPadding.pad U (UnaryTemplate.tape key)).length≤U
    rw [ZeroPadding.pad_length]
    apply max_le (le_refl _)
    simp only [UnaryTemplate.tape,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega
 have h:=(PCJ45bee56da9f34d5a_HeaderRewind.clear_run 2 (fun _ :Fin 2=>1) A U (by intro i;omega) hA).dock clearSlots (by decide)
  (heads out.length 1 1) (bank a B p w F U n key v key source out)
  (by intro i;fin_cases i <;>rfl)
  (by
   intro i;fin_cases i
   · rfl
   · rfl
   · exact at62 a B p w F U n key v key source out
   · exact at63 a B p w F U n key v key source out)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads clearSlots (by decide)
   · intro i;fin_cases i <;>rfl
   · intro i hi
     rw [heads_arity_away _ 1 0 1 i (fun he=>hi 0 he.symm),heads_index_away _ 0 1 0 i (fun he=>hi 1 he.symm)]
 · apply HierarchyAllocation.install_eq clearSlots (by decide)
   · intro i;fin_cases i
     · exact compare_zero U (by omega)
     · exact unary_zero U (by omega)
     · exact at62 a B p w F U 0 0 v key source out
     · exact at63 a B p w F U 0 0 v key source out
   · intro i hi
     exact (bank_away a B p w F U n 0 key 0 v key source out i
       (fun he=>hi 0 he.symm) (fun he=>hi 1 he.symm)).symm

def budget {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length) (w F U v :Nat):=
 ((2*PCPPQueryNatural.budget n+4*U+10)+1+(MatrixUnaryTemplate.budget v i.val+2*U+5))+1+
 PCJ45bee56da9f34d5a_SelectedPowerRun.budget gs i w F U+1+(4*U+9)

theorem run {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length)
 (a B p w F U v :Nat) (out :List Bool)
 (hu : PCPPQueryNatural.budget n<U) (hi : i.val<2^v) (hindex : MatrixUnaryTemplate.budget v i.val<U)
 (hpay : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
 (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
 (hg : (exactWord (gs.get i)).length+2≤U)
 (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w) (hB : B<2^w)
 (hw : ∀j,C10NativeResidueCallback.coreBudget false ((gs.get i).weight j) w+1≤F)
 (ht : C10NativeResidueCallback.coreBudget true (gs.get i).target w+1≤F)
 (hU : 1024*(w+1)^2+2≤U) :
 Step machine (budget gs i w F U v)
  (heads out.length 0 0) (bank a B p w F U 0 0 v i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out)
  (heads (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length 0 0)
  (bank ((a*B)%p) B p w F U 0 0 v i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
   (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))) :=by
 have hn:n+2≤U:=by unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hu;omega
 have hk:i.val+2≤U:=by unfold MatrixUnaryTemplate.budget at hindex;omega
 have first:=arity_run gs a B p w F U v i.val out hu
 have second:=index_run a B p w F U n v i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out hi hindex
 have emit0:=(PCJ45bee56da9f34d5a_SelectedPowerRun.run gs i a B p w F U out hn hpay hf hg hp hpw ha hB hw ht hU).embed
  (fun _ :Fin 2=>0) (![frame (binary v i.val),List.replicate v true] :Fin 2→List Bool)
 have third:Step emit (PCJ45bee56da9f34d5a_SelectedPowerRun.budget gs i w F U)
  (heads out.length 1 1) (bank a B p w F U n i.val v i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) out)
  (heads (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length 1 1)
  (bank ((a*B)%p) B p w F U n i.val v i.val (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
   (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))):=by
  exact (emit0.congr_in (heads_ready _) rfl).congr (heads_ready _) rfl
 have last:=clear_run ((a*B)%p) B p w F U n i.val v (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
  (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))) hn hk
 exact ((first.seq second).seq third).seq last
end
end PCJ45bee56da9f34d5a_SelectedPowerReady
