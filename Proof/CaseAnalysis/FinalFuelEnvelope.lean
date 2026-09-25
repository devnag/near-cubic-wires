import Proof.CaseAnalysis.FinalFuelRepin

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The defect: the POLYNOMIAL bucket can never hold one `2^q` call -/

/-! ## Section 2  The repair: the HOT bucket already holds it, and that is where it lands -/

/-- **The companion, machine-checked.**  The very same `polyFuel C d N` -- at every degree
`d + 1 <= k + 2` the re-pin admits -- fits inside ONE residual table factor
`2 ^ (q - kappa * L_q)`, the `hot`-bucket cell that `ledger_of_parts`' `hrow` binder
(`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) allows.  That cell IS the paper's
`2^q/q^sigma` (`paper.tex:3555-3557`), by `kappa >= h_D + sigma + c_1`
(`paper.tex:2303-2307`).

So the envelope was never too small: `2 ^ (q - kappa*L_q)` holds what `A*(N+1)^a` cannot, and
`preFuel`/`cost` ALREADY reach it -- `ledger_of_parts` routes the whole `stageFuel` through
`stageFuel_core` (`Proof/CaseAnalysis/FinalSupplierFuel.lean`) into `hot`, while `hpoly`'s
`A*(N+1)^a` carries only `hrest`'s docked emit and tail budget.  This is REFUEL's own
`rowFuel_le_table` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) with the `rowFuel` wrapper
removed, so that the quantity named is the budget itself. -/
theorem polyFuel_le_table (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2)
    (hN : repinOnset sources k r degree C ≤ N) :
    polyFuel C d N
      ≤ 2 ^ (widthAt sources k N
          - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1)) := by
  refine le_trans ?_ (rowFuel_le_table sources k r degree C d N hd hN)
  show polyFuel C d N ≤ 2 * polyFuel C d N + 2 * polyFuel C d N + 18
  omega


end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope
