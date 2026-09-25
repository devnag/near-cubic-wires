import Proof.Rows.VerdictFinish

/-! # Rows C3(d) prerequisite: the THR traversal input depends on the cell only at port 109

**Consumer.** The cropped cell loop (map duty C3(d)): between two cells only the cell's assignment
`x = joinInput live (fun _ => false) (printerPoint …)` changes, and `RowsCellReload.cell_step` reloads
the whole 254-port bank from resident masters. For the masters to stay resident across cells, exactly
one master may change per cell. This module proves that: `ThresholdTraversal.input … x` equals the
input at any other assignment `x'` updated at port 109 to `List.ofFn x`
(the assignment enters only through `MinimumGateCell.extra`, `…_MinimumGateCell.lean:25`).

**Paper.** `paper.tex:1209-1211` ("the actual residual offset `f_{g,p}(z)` selects one cell"): the
column `z` is the only per-cell datum of an external row. **Budget.** None (a bank identity).
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CellInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem addCases_update_left {m n : Nat} {α : Type} (A : Fin m → α) (B : Fin n → α) (k : Fin m)
    (v : α) :
    Fin.addCases (motive := fun _ => α) (Function.update A k v) B =
      Function.update (Fin.addCases (motive := fun _ => α) A B) (Fin.castAdd n k) v := by
  funext i
  refine Fin.addCases (m:=m) (n:=n) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    by_cases h : j = k
    · subst h
      simp
    · rw [Function.update_of_ne h, Function.update_of_ne (fun he => h (Fin.castAdd_inj.mp he)),
        Fin.addCases_left]
  · simp only [Fin.addCases_right]
    have hne : (Fin.natAdd m j : Fin (m+n)) ≠ Fin.castAdd n k := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := k.isLt
      omega
    rw [Function.update_of_ne hne, Fin.addCases_right]

theorem addCases_update_right {m n : Nat} {α : Type} (A : Fin m → α) (B : Fin n → α) (k : Fin n)
    (v : α) :
    Fin.addCases (motive := fun _ => α) A (Function.update B k v) =
      Function.update (Fin.addCases (motive := fun _ => α) A B) (Fin.natAdd m k) v := by
  funext i
  refine Fin.addCases (m:=m) (n:=n) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    have hne : (Fin.castAdd n j : Fin (m+n)) ≠ Fin.natAdd m k := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := j.isLt
      omega
    rw [Function.update_of_ne hne, Fin.addCases_left]
  · simp only [Fin.addCases_right]
    by_cases h : j = k
    · subst h
      simp
    · have hne : (Fin.natAdd m j : Fin (m+n)) ≠ Fin.natAdd m k := by
        intro he
        apply h
        apply Fin.ext
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd] at hv
        omega
      rw [Function.update_of_ne h, Function.update_of_ne hne, Fin.addCases_right]

theorem extra_x {q : Nat} (live : Finset (Fin q)) (x x' : BitInput q) (H : Nat) :
    PCJ45bee56da9f34d5a_MinimumGateCell.extra live x H =
      Function.update (PCJ45bee56da9f34d5a_MinimumGateCell.extra live x' H) 1 (List.ofFn x) := by
  funext i
  fin_cases i <;> rfl

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q))
  {cutoff : Nat} (prime : PrimeIndex cutoff) (o : Fin prime.val) (T L target w F U v : Nat)

/-- **The cell enters the traversal input only at port 109.** -/
theorem input_x (x x' : BitInput r.q) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v =
      Function.update
        (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x' prime o T L target w F U v)
        109 (List.ofFn x) := by
  unfold PCJ45bee56da9f34d5a_ThresholdTraversal.input PCJ45bee56da9f34d5a_StreamCompare.bank
    PCJ45bee56da9f34d5a_StreamPair.input PCJ45bee56da9f34d5a_StreamPair.flagStart
    PCJ45bee56da9f34d5a_NativeFamilyCount.bank PCJ45bee56da9f34d5a_CircuitFlagBank.bank
    PCJ45bee56da9f34d5a_NativeCircuitCount.bank PCJ45bee56da9f34d5a_CountedGateCell.bank
    PCJ45bee56da9f34d5a_FramedGateBank.bank PCJ45bee56da9f34d5a_FramedGateBank.coreBank
  rw [extra_x I x x']
  simp only [addCases_update_left, addCases_update_right]
  rfl

theorem input_109 (x : BitInput r.q) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 109 =
      List.ofFn x := by
  rw [input_x a r four sel I prime o T L target w F U v x x, Function.update_self]

theorem input_ne (x x' : BitInput r.q) (i : Fin 254) (hi : i ≠ 109) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x' prime o T L target w F U v i := by
  rw [input_x a r four sel I prime o T L target w F U v x x', Function.update_of_ne hi]

end
end RowsConstruction.CellInput
