import Proof.CaseAnalysis.WitnessFamilyResourcesPolicy

/-! Consumer-first closure of the unchanged FamilyCold numerical interface.
The P/H constants depend on the fixed sources and policies, never on a
hierarchy clock. Source/cache/driver production is still physically paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth PaddedRunnerBudgetClosure
open SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem source_fits (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies K E : ℕ)
    (hbudget : ∀ N,capacity (sourceScale a qc qd od D delta copies N) ≤ K*(N+1)^E)
    {n R Q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin Q→Fin n→ProjectedRandomBit R) (formula : ThreeCNF Q)
    (N : ℕ) (bits arity : List Bool) (hR : R ≤ N) (hbits : bits.length ≤ N)
    (harity : arity.length ≤ N+1) (hQ : Q ≤ qc*(R+1)^qd)
    (ho : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound od R) :
    let p:=a.output (PCPPSubstitution.sourceRequest a oracle projections formula)
    Fits (K*(N+1)^E) (p.systematicBits+p.auxiliaryBits)
      (coefficientCap delta copies D R p.clauseBits) (termCap delta copies D R p.clauseBits)
      (CloseoutMassThreshold.literalWidth delta copies) bits arity := by
  obtain ⟨hn,_hv,hc,ht,hk⟩:=source_bounds a qc qd od D delta copies oracle projections formula N hR hQ ho
  exact fits _ _ _ _ _ _ bits arity (hbudget N) (hbits.trans (by omega)) (harity.trans hn) hc ht hk

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
