import Proof.Rows.UniformFullGate
import Proof.Rows.MinimumGateCell

/-! The same actual minimizing-mask/evaluate/erase cell uses uniform reserve
masters across consecutive original gates. No machine is changed or duplicated. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformMinimumGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure NearCubicWires.ExtIncidence NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open PCJ45bee56da9f34d5a_MinimumGateCell (member minInput extra extraHeads heads slots slots_injective eraseSlots produce evaluate erase machine)
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine
def bank {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (w H R U : Nat) (mask out : List Bool) : Fin 114→List Bool :=
  Fin.addCases (m:=108) (n:=6) (motive:=fun _=>List Bool) (cold (words (ZeroPadding.pad H (source g)) (ZeroPadding.pad H mask) q w (HardwireBudget.C w)
    (R)) U out) (extra live x H)
theorem bank_away {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (w H R U : Nat) (mask next out : List Bool) (i : Fin 114) (hi : i≠1) :
    bank g live x w H R U mask out i=bank g live x w H R U next out i := by
  fin_cases i <;>first |rfl |contradiction

theorem produce_run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (out : List Bool) (w H R U : Nat)
    (hw : ∀i,natBitLength (g.weight i).natAbs ≤ w) (hF : 2*w+5 ≤ H)
    (hs : ((List.ofFn g.weight).flatMap intWord).length ≤ H) (hq : q ≤ H) :
    Step produce (PCJ45bee56da9f34d5a_MinimumMaskRun.budget q (2*w+5)+4*H+10)
      (heads out) (bank g live x w H R U [] out)
      (heads out) (bank g live x w H R U (List.ofFn (minInput g live x)) out) := by
  have hf : ∀z∈List.ofFn g.weight,2*natBitLength z.natAbs+5 ≤ 2*w+5 := by
    intro z hz;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz;have h:=hw i;omega
  have base := (PCJ45bee56da9f34d5a_MinimumMaskReady.run (List.ofFn g.weight) (intWord (g.threshold-1))
    (member live) (List.ofFn x) (2*w+5) H hf hF hs (by simpa using hq)).pad (fun i : Fin 8=>if i=0 then H else 0)
  have hout := PCJ45bee56da9f34d5a_MinimumMaskMeaning.output_eq g live x
  simp only [List.length_ofFn,member,hout] at base
  have h := base.dock slots slots_injective (heads out) (bank g live x w H R U [] out)
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>first |rfl |exact (ZeroPadding.pad_zero _).symm)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq slots slots_injective
    · intro i;fin_cases i <;>first |rfl |exact (ZeroPadding.pad_zero _).symm
    · intro i hi
      exact (bank_away g live x w H R U [] (List.ofFn (minInput g live x)) out i (fun h=>hi 4 h.symm)).symm

theorem evaluate_run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (out : List Bool) (w H R U : Nat)
    (hw : 0 < w) (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w)
    (hc : HardwireBudget.C w+1 ≤ U) (hd : HardwireBudget.D q w ≤ U)
    (hr : R+1 ≤ U)
    (hcap : PCJ45bee56da9f34d5a_FullGateBounds.reserve g (minInput g live x) w ≤ R)
    (hu : ∀i,(words (source g) (List.ofFn (minInput g live x)) q w (HardwireBudget.C w) (R) i).length ≤ U) :
    Step evaluate (PCJ45bee56da9f34d5a_UniformFullGate.budget g (minInput g live x) w R U)
      (heads out) (bank g live x w H R U (List.ofFn (minInput g live x)) out)
      (heads (out++[residualConstant g live x]))
      (bank g live x w H R U (List.ofFn (minInput g live x)) (out++[residualConstant g live x])) := by
  have h := (PCJ45bee56da9f34d5a_UniformFullGate.run g (minInput g live x) out w H R U hw hm hcap hc hd hr hu).embed extraHeads (extra live x H)
  rw [show g.eval (minInput g live x)=residualConstant g live x from PCJ45bee56da9f34d5a_MinimumAssignment.eval_eq g live x] at h
  exact h

theorem erase_run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (out : List Bool) (w H R U : Nat) (hq : q ≤ H) :
    Step erase (2*H+4) (heads out) (bank g live x w H R U (List.ofFn (minInput g live x)) out)
      (heads out) (bank g live x w H R U [] out) := by
  have hlen : (ZeroPadding.pad H (List.ofFn (minInput g live x))).length ≤ H := by
    simp only [ZeroPadding.pad_length,List.length_ofFn];exact max_le le_rfl hq
  have h := (Step.of_ready (RecoveryScratchErase.erase_ready H (H+1)
    (![ZeroPadding.pad H (List.ofFn (minInput g live x))] : Fin 1→List Bool)
    (by intro i;fin_cases i;exact hlen))).dock eraseSlots (by decide) (heads out)
      (bank g live x w H R U (List.ofFn (minInput g live x)) out)
      (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
  · apply HierarchyAllocation.install_eq eraseSlots (by decide)
    · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
    · intro i hi
      exact (bank_away g live x w H R U (List.ofFn (minInput g live x)) [] out i (fun h=>hi 0 h.symm)).symm

theorem run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (out : List Bool) (w H R U : Nat)
    (hw : 0 < w) (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w)
    (hF : 2*w+5 ≤ H) (hs : ((List.ofFn g.weight).flatMap intWord).length ≤ H) (hq : q ≤ H)
    (hc : HardwireBudget.C w+1 ≤ U) (hd : HardwireBudget.D q w ≤ U)
    (hr : R+1 ≤ U)
    (hcap : PCJ45bee56da9f34d5a_FullGateBounds.reserve g (minInput g live x) w ≤ R)
    (hu : ∀i,(words (source g) (List.ofFn (minInput g live x)) q w (HardwireBudget.C w) (R) i).length ≤ U) :
    Step PCJ45bee56da9f34d5a_MinimumGateCell.machine (PCJ45bee56da9f34d5a_MinimumMaskRun.budget q (2*w+5)+6*H+
      PCJ45bee56da9f34d5a_UniformFullGate.budget g (minInput g live x) w R U+16)
      (heads out) (bank g live x w H R U [] out)
      (heads (out++[residualConstant g live x])) (bank g live x w H R U [] (out++[residualConstant g live x])) := by
  obtain ⟨hf,_,_,_,_,_⟩:=of_magnitude g (minInput g live x) w hw hm
  have hi : ∀i,natBitLength (g.weight i).natAbs ≤ w := by
    intro i;exact hf _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have h:=((produce_run g live x out w H R U hi hF hs hq).seq
    (evaluate_run g live x out w H R U hw hm hc hd hr hcap hu)).seq
      (erase_run g live x (out++[residualConstant g live x]) w H R U hq)
  unfold PCJ45bee56da9f34d5a_MinimumGateCell.machine
  convert h using 1;omega
end
end PCJ45bee56da9f34d5a_UniformMinimumGate
