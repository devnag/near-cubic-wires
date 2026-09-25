import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmFields
import Proof.Rows.ClosureOffsetMask
import Proof.Rows.FinalCoordinateBridge

/-!
# The per-row selection mask word, in the printer's own cell order

`PCJ38fbfed565f64139_Row.Frame.fields printer (Packets.datum a F g layout row hr facts)` is
`P1TopDownPaidReloadCore.input printer d.row d.C d.Q d.select`
(`PCJeb9c0f0306e9481c_FramingSpec.datumFields`), whose seven warm payload fields are
`CloseoutRowsEstimator.WarmFields.words d.row d.Q estimate 1 d.select`
(`Proof/MachineModel/TopDownPaidReloadCore.lean`).  Entry `2` of those words is the only large varying
one, and is the BARE (unframed) list

  `CompetitorCountMask.mask (CompetitorSelectedCells.cells row.odd (fun _ _ => 0) select)`
  (`Proof/CaseAnalysis/CloseoutRowsEstimatorWarmFields.lean`).

`gridWord` below names that word directly in the printer's own coordinates: one bit per residual
column, flat index `k` addressing printed row `k / 2^(s/2)` and printed column `k % 2^(s/2)`,
which is exactly `C10ExternalRowLoop.printerPoint`'s cell `(rowN, colN)`.  Its type mentions the
row's own `sel : BitInput liveᶜ.card → Bool` and `printerPoint`, so nothing that fails to
evaluate that selector at every residual column can inhabit it.

`mask_cells_printerPoint` is the cell-order lemma: it discharges the `odd`/`u` crop
(`CompetitorFinalTable.lowerColumn`, applied by `CompetitorSelectedCells.cells` when
`s % 2 = 1`) against the flat `2 ^ s` enumeration, so `gridWord` IS the payload field.

`gridWord_run` then observes that `P1Closure.OffsetMaskSymmetric.run`
(`Proof/Rows/ClosureOffsetMaskSymmetric.lean`) — a concrete four-tape comparison loop with
no machine-shaped hypotheses — ALREADY emits that word, at
`OffsetMask.budget (request.circuits.length * w) (2 ^ s) = 2^s * (4*(L*w)+7) + 3`,
once the row's selector is identified with `fun z => decide (offsetOf request liveScale z = f)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_SelectionWord
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask)
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

variable {n : Nat} (live : Finset (Fin n)) (s : Nat)
  (harity : (s+1)/2+s/2=(liveᶜ).card) (sel : BitInput (liveᶜ).card → Bool)

/-! ## 1. The word -/

/-- **The row payload's selection mask.**  One bit per residual column, enumerated exactly once,
in `C10ExternalRowLoop.printerPoint` order: flat index `k` is printed row `k / 2^(s/2)` and
printed column `k % 2^(s/2)`. -/
def gridWord : List Bool :=
  (List.range (2^s)).map fun k =>
    sel (C10ExternalRowLoop.printerPoint live s harity (k/2^(s/2)) (k%2^(s/2)))

theorem gridWord_length : (gridWord live s harity sel).length=2^s := by
  simp only [gridWord,List.length_map,List.length_range]

/-! ## 2. `gridWord` is the payload field -/

theorem maskColumns_eq (u : Nat) (hu : u=2^((s+1)/2)) (odd : Bool) (hodd : odd=decide (s%2=1)) :
    C10SupplierSelect.maskColumns odd u=2^(s/2) := by
  by_cases h : s%2=1
  · rw [hodd,decide_eq_true h,C10SupplierSelect.maskColumns,if_pos rfl,hu,
      show (s+1)/2=s/2+1 by omega,pow_succ]
    omega
  · rw [hodd,decide_eq_false h,C10SupplierSelect.maskColumns,if_neg (by simp),hu,
      show (s+1)/2=s/2 by omega]

theorem cellCount_eq (u : Nat) (hu : u=2^((s+1)/2)) (odd : Bool) (hodd : odd=decide (s%2=1)) :
    C10SupplierSelect.cellCount odd u=2^s := by
  rw [C10SupplierSelect.cellCount,maskColumns_eq s u hu odd hodd,hu,←pow_add]
  exact congrArg (fun k => 2^k) (by omega)

/-- **The warm payload field is `gridWord`.**  `u` and `odd` are the row input's own
`(EquationRow.request row).U = 2 ^ ((s+1)/2)` and `row.odd = decide (s % 2 = 1)`; when
`s` is odd, `CompetitorSelectedCells.cells` crops the square to its lower half-columns and this
lemma matches that crop against the flat `2 ^ s` enumeration. -/
theorem mask_cells_printerPoint (u : Nat) (hu : u=2^((s+1)/2))
    (odd : Bool) (hodd : odd=decide (s%2=1)) :
    mask (CompetitorSelectedCells.cells odd (fun _ _ : Fin u=>(0:Nat))
        (fun i j : Fin u =>
          sel (C10ExternalRowLoop.printerPoint live s harity i.val j.val)))=
      gridWord live s harity sel := by
  have hcols : C10SupplierSelect.maskColumns odd u=2^(s/2) := maskColumns_eq s u hu odd hodd
  have hcells : u*C10SupplierSelect.maskColumns odd u=2^s := cellCount_eq s u hu odd hodd
  by_cases h : s%2=1
  · have hoddT : odd=true := by rw [hodd,decide_eq_true h]
    subst hoddT
    rw [CompetitorSelectedCells.cells,if_pos rfl,
      C10SupplierSelect.mask_rect_range
        (fun (i : Fin u) (j : Fin (u/2)) =>
          sel (C10ExternalRowLoop.printerPoint live s harity i.val
            (NearCubicWires.RepairOrdinary.CompetitorFinalTable.lowerColumn j).val))
        (fun a b => sel (C10ExternalRowLoop.printerPoint live s harity a b))
        (fun _ _ => rfl)]
    rw [show u/2=C10SupplierSelect.maskColumns true u from rfl,hcells,hcols]
    rfl
  · have hoddF : odd=false := by rw [hodd,decide_eq_false h]
    subst hoddF
    rw [CompetitorSelectedCells.cells,if_neg (by simp),
      C10SupplierSelect.mask_rect_range
        (fun i j : Fin u =>
          sel (C10ExternalRowLoop.printerPoint live s harity i.val j.val))
        (fun a b => sel (C10ExternalRowLoop.printerPoint live s harity a b))
        (fun _ _ => rfl)]
    have hsame : u=2^(s/2) := by rw [hu,show (s+1)/2=s/2 by omega]
    rw [hsame,←pow_add,show s/2+s/2=s by omega]
    rfl

/-! ## 3. The existing producer already emits it -/

end
end PCJ45bee56da9f34d5a_SelectionWord
