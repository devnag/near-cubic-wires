import Proof.Packets.FinalThresholdOneHotTargetArithmetic
import Proof.Rows.PhysicalFocusBoundary
import Proof.MachineModel.ClosureLocalSupport

/-! Both actual sign/range flags for a delta window target. The total residue
is produced even outside the valid range; the two physical flags select the
provider versus the physically generated zero polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaTargetGuard
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

def compareSlots : Fin 4→Fin 15 := ![10,12,13,14]
def machine := Composition.machine (TapeEmbedding.machine 3 C10ThresholdOneHotTargetArithmetic.machine)
  (RecoveryFocus.machine compareSlots CompetitorSignedDecision.compareMachine)
def extras (u width R : Nat) : Fin 3→List Bool := ![frame (binary u width),[],List.replicate R false]
def input (u c parent child width R : Nat) : Fin 15→List Bool :=
  Fin.addCases (m:=12) (n:=3) (motive:=fun _=>List Bool) (C10ThresholdOneHotTargetArithmetic.input u c parent child) (extras u width R)
def budget (u : Nat) := 28*u+34

theorem compare_ready (u a b R : Nat) (ha : a<2^u) (hb : b<2^u) (hr : 2*u+1≤R) :
    Step CompetitorSignedDecision.compareMachine (4*u+4) (fun _=>0)
      ![frame (binary u a),frame (binary u b),[],List.replicate R false] (fun _=>0)
      ![frame (binary u a),frame (binary u b),[decide (a≤b)],List.replicate R false] := by
  have h:=(Step.of_ready (CompetitorSignedDecision.compare_ready u a b ha hb)).pad
    (![0,0,0,R] : Fin 4→Nat)
  have he : ZeroPadding.pad R (List.replicate (2*u+1) false)=List.replicate R false := by
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
    congr 1;omega
  exact (h.congr_in rfl (by funext i;fin_cases i <;>simp [he])).congr rfl
    (by funext i;fin_cases i <;>simp [he])

theorem run (u c parent child width R : Nat) (hsum : c+parent<2^u)
    (hchild : 2*child<2^u) (hwidth : width<2^u) (hr : 2*u+1≤R) :
    ∃ T,Step machine (budget u) (fun _=>0) (input u c parent child width R) (fun _=>0) T ∧
      T 0=frame (binary u c) ∧ T 1=frame (binary u parent) ∧ T 2=frame (binary u child) ∧
      T 8=[decide (2*child≤c+parent)] ∧
      T 10=frame (binary u (CompetitorSignedResidue.residue u u (c+parent) (2*child))) ∧
      T 12=frame (binary u width) ∧
      T 13=[decide (CompetitorSignedResidue.residue u u (c+parent) (2*child)≤width)] ∧
      (2*child≤c+parent→T 10=frame (binary u (c+parent-2*child))) := by
  obtain ⟨A,first,a0,a1,a2,_,_,a8,a10,atarget⟩:=C10ThresholdOneHotTargetArithmetic.run u c parent child hsum hchild
  let stage : Fin 15→List Bool := Fin.addCases (m:=12) (n:=3) (motive:=fun _=>List Bool) A (extras u width R)
  have f:=first.embed (fun _ : Fin 3=>0) (extras u width R)
  have hh : Fin.addCases (m:=12) (n:=3) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)=(fun _=>0) := by
    funext i;fin_cases i <;>rfl
  rw [hh] at f
  have hres : CompetitorSignedResidue.residue u u (c+parent) (2*child)<2^u :=
    Nat.mod_lt _ (by positivity)
  have cr:=compare_ready u _ width R hres hwidth hr
  have last:=cr.dock compareSlots (by decide) (fun _=>0) stage (by intro j;rfl) (by
    intro j;fin_cases j
    · exact a10
    all_goals rfl)
  rw [dockH_existing compareSlots (fun _=>0) (fun _=>0) (by intro j;rfl)] at last
  have whole:=f.seq last
  have he : C10ThresholdOneHotTargetArithmetic.budget u+1+(4*u+4)=budget u := by unfold C10ThresholdOneHotTargetArithmetic.budget budget;omega
  rw [he] at whole
  refine ⟨_,whole,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other compareSlots stage _ 0 (by decide)).trans a0
  · exact (install_other compareSlots stage _ 1 (by decide)).trans a1
  · exact (install_other compareSlots stage _ 2 (by decide)).trans a2
  · exact (install_other compareSlots stage _ 8 (by decide)).trans a8
  · exact install_slot compareSlots (by decide) _ _ 0
  · exact install_slot compareSlots (by decide) _ _ 1
  · exact install_slot compareSlots (by decide) _ _ 2
  · intro hlo
    have hi:=install_slot compareSlots (by decide) stage
      ![frame (binary u (CompetitorSignedResidue.residue u u (c+parent) (2*child))),
        frame (binary u width), [decide (CompetitorSignedResidue.residue u u (c+parent) (2*child)≤width)], List.replicate R false] 0
    exact hi.trans (by rw [C10ThresholdOneHotTargetArithmetic.residue_of_le u _ _ hsum hlo];rfl)

/-- The two physically computed flags agree with the original optional target. -/
theorem flags_exact (u n w parent child : Nat) (hsum : min n w+parent<2^u) :
    (2*child≤ min n w+parent ∧
      CompetitorSignedResidue.residue u u (min n w+parent) (2*child)≤2*w) ↔
    SupplierListPolynomial.deltaTarget? n w parent child=some (min n w+parent-2*child) := by
  rw [C10ThresholdOneHotTargetArithmetic.target_option]
  by_cases hlo : 2*child≤ min n w+parent
  · rw [C10ThresholdOneHotTargetArithmetic.residue_of_le u _ _ hsum hlo]
    simp only [hlo,true_and,if_true]
    by_cases hhi : min n w+parent-2*child≤2*w <;>simp [hhi]
  · simp [hlo]


/-- Padding retains the exact guard result and bounds every scratch word,
allowing the next physical cleanup to overwrite exactly R cells. -/
theorem padded_run (u c parent child width R : Nat) (hsum : c+parent<2^u)
    (hchild : 2*child<2^u) (hwidth : width<2^u) (hr : budget u+1≤R) :
    ∃ T,Step machine (budget u) (fun _=>0)
      (fun i=>ZeroPadding.pad R (input u c parent child width R i)) (fun _=>0) T ∧
      (∀i,(T i).length=R) ∧
      T 0=ZeroPadding.pad R (frame (binary u c)) ∧
      T 1=ZeroPadding.pad R (frame (binary u parent)) ∧
      T 2=ZeroPadding.pad R (frame (binary u child)) ∧
      T 8=ZeroPadding.pad R [decide (2*child≤c+parent)] ∧
      T 10=ZeroPadding.pad R (frame (binary u (CompetitorSignedResidue.residue u u (c+parent) (2*child)))) ∧
      T 12=ZeroPadding.pad R (frame (binary u width)) ∧
      T 13=ZeroPadding.pad R [decide (CompetitorSignedResidue.residue u u (c+parent) (2*child)≤width)] := by
  have hu : 2*u+1≤R := by unfold budget at hr;omega
  obtain ⟨T,h,h0,h1,h2,h8,h10,h12,h13,_⟩:=run u c parent child width R hsum hchild hwidth hu
  refine ⟨fun i=>ZeroPadding.pad R (T i),h.pad (fun _=>R),?_,
    congrArg (ZeroPadding.pad R) h0,congrArg (ZeroPadding.pad R) h1,
    congrArg (ZeroPadding.pad R) h2,congrArg (ZeroPadding.pad R) h8,
    congrArg (ZeroPadding.pad R) h10,congrArg (ZeroPadding.pad R) h12,
    congrArg (ZeroPadding.pad R) h13⟩
  intro i
  have hi : (input u c parent child width R i).length≤R := by
    fin_cases i <;>simp [input,C10ThresholdOneHotTargetArithmetic.input,extras,
      Fin.addCases,frame_length,binary_length] <;>omega
  have fit:=P1Closure.LocalSupport.step_fits h i R hi (by omega)
  simp only [ZeroPadding.pad_length,Nat.max_eq_left fit]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaTargetGuard
