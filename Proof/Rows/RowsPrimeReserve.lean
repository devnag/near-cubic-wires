import Proof.Rows.RowsPartsFill

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.PrimeReserve
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.BlockPlatform
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- The prime value is at most the cutoff, or the off-range flag `1`. -/
theorem primeAt_le (c u : Nat) : NearCubicWires.PacketsGlue.primeAt c u ≤ c+1 := by
  by_cases hu : u < NearCubicWires.PacketsGlue.PrimeCount.pc c
  · have := (NearCubicWires.PacketsGlue.RequestMeta.primeAt_spec c u hu).2.1
    omega
  · rw [NearCubicWires.PacketsGlue.RequestMeta.primeAt_off c u (by omega)]
    omega

theorem nextP_le (c p : Nat) : RowsConstruction.ThrPrime.nextP c p ≤ c+2 := by
  have h := primeAt_le c (NearCubicWires.PacketsGlue.PrimeCount.pc p)
  unfold RowsConstruction.ThrPrime.nextP NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf
  omega

/-- The reserve's coefficient. -/
def rpK : Nat := 16384

/-- **The prime stage's uniform cost bound**, at `w = 12T+19` (`KeyTop.wT`). -/
theorem psCost_le (T c p : Nat) (hp : p ≤ c) :
    RowsConstruction.ThrPrime.psCost (12*T+19) c p + 1 ≤ rpK*(T+c+1)^3 := by
  have hnpo := primeAt_le c (NearCubicWires.PacketsGlue.PrimeCount.pc p)
  have hm : NearCubicWires.PacketsGlue.RequestMeta.nextPrimeOf c p ≤ c+1 := hnpo
  have hnp := nextP_le c p
  have hnpm := NearCubicWires.PacketsGlue.RequestMeta.next_cost c p
  have hy : 1 ≤ T+c+1 := by omega
  have hy2 : T+c+1 ≤ (T+c+1)^2 := by nlinarith
  have hy3 : (T+c+1)^2 ≤ (T+c+1)^3 := by nlinarith
  have h3 : (c+p+3)^3 ≤ 125*(T+c+1)^3 := by
    have h5 : c+p+3 ≤ 5*(T+c+1) := by omega
    calc (c+p+3)^3 ≤ (5*(T+c+1))^3 := Nat.pow_le_pow_left h5 3
      _ = 125*(T+c+1)^3 := by ring
  have hpw : p*(8*(12*T+19)+10) ≤ 162*(T+c+1)^2 := by
    have h1 : 8*(12*T+19)+10 ≤ 162*(T+c+1) := by omega
    calc p*(8*(12*T+19)+10) ≤ (T+c+1)*(162*(T+c+1)) := Nat.mul_le_mul (by omega) h1
      _ = 162*(T+c+1)^2 := by ring
  have hcf : RowsConstruction.ThrPrime.nextP c p*(4*(12*T+19)+11) ≤ 261*(T+c+1)^2 := by
    have h1 : 4*(12*T+19)+11 ≤ 87*(T+c+1) := by omega
    calc RowsConstruction.ThrPrime.nextP c p*(4*(12*T+19)+11) ≤ (3*(T+c+1))*(87*(T+c+1)) :=
          Nat.mul_le_mul (by omega) h1
      _ = 261*(T+c+1)^2 := by ring
  unfold RowsConstruction.ThrPrime.psCost NearCubicWires.RepairOrdinary.CloseoutCaseTwo.BinaryField.budget
    NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SliceFrame.budget
    NearCubicWires.RepairOrdinary.MatrixUnaryTemplate.budget
    NearCubicWires.RepairSource.ProjectionNormalization.Counter.budget PCJ45bee56da9f34d5a_CountFlags.budget rpK
  omega

def rpOf (a : DecompositionAlgorithm) : Request → Nat
  | .thr r four L target =>
      UnaryCalc.value 3 rpK (RowsConstruction.ThrWidth.T a r four L target + KeySucc.cut a r target)
  | _ => 0

/-- **`Holes.hRp`.** -/
theorem hRp (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) :
    ∀ p, p ≤ KeySucc.cut a r target →
      RowsConstruction.ThrPrime.psCost (KeyTop.wT a r four L target) (KeySucc.cut a r target) p + 1 ≤
        rpOf a (.thr r four L target) := by
  intro p hp
  have h := psCost_le (RowsConstruction.ThrWidth.T a r four L target) (KeySucc.cut a r target) p hp
  change _ ≤ rpK*(RowsConstruction.ThrWidth.T a r four L target + KeySucc.cut a r target+1)^3
  exact h

end
end RowsConstruction.PrimeReserve
