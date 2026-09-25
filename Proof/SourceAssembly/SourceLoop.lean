import Proof.SourceAssembly.SourceCycle

/-! # The loop layer, part 1: one cycle's exit fixed BEFORE its entry is known

**Consumer.** `SourceTrace._hrefill` (`closeout-five-checks-20260921/RCFiveSourceTrace.lean:196`) quantifies over
every family output `Z`, while the witness banks `H (j+1)`, `A (j+1)` are chosen before `Z`. So one cycle's exit must
not depend on the refill's entry, and it does not: everything after the prologue's clear is determined by the
clear's exit. `cycle_prepared_all` therefore fixes `(H', A')` from the PROLOGUE EXIT `(H1, A1)` alone and proves
`Prepared` for EVERY prologue run that reaches `(H1, A1)`.

H1's window needs the dirt bound from the post-prologue run, and `Prepared` hides the internal banks. So the same
`(H', A')` also comes with the `Prepared` of the halt-prologue code started at `(H1, A1)`. `prepared_step` turns
that into a `Step` of the cycle machine (`MaskFamilyCode.project → FamilyCode.project → Cached.run`).

**Paper.** None names a tape. The consumers are `_hrefill`/`_hfirst` and H1. **Budget**: as in `cycle_prepared`.
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open SupplierEstimator SupplierPipeline NearCubicWires.P1Closure
namespace NearCubicWires.SourceConstruction.Cycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-- A prepared cycle runs: the cycle machine's `Step` at the same fuel and banks. -/
theorem prepared_step {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
    {rows : RowProducer selector a printer} {U : Nat} (p : MaskFamilyCode mask packet rows U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat) (H H' : Fin U → Nat) (A A' : Fin U → List Bool)
    (h : p.Prepared ds fuel H H' A A') :
    Step (PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code p.base.cached)) fuel H A H' A' :=
  PCJ38fbfed565f64139_Cached.run p.base.cached ds fuel H H' A A'
    (FamilyCode.project p.base ds fuel H H' A A' (MaskFamilyCode.project p ds fuel H H' A A' h))

end
end NearCubicWires.SourceConstruction.Cycle
end
