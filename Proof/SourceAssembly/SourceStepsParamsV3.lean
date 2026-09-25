import Proof.Packets.BudgetSeamScalars
import Proof.Packets.SrcCapsPow2
import Proof.SourceAssembly.SourceStepsClassR

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton NearCubicWires.SourceSkeleton.ClassR
namespace NearCubicWires.SourceSkeleton.ClassV3
noncomputable section

/-! ## 1. The gauge v3 and `KFc3` -/

section gauge
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

def gE0v3 : ParNat := fun s g hg hh p =>
  gE0 selector mask packets rows s g hg hh p +
    (reqE s p + 1) * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) + reqE s p

/-- **The gauge exponent v3.** -/
def gEv3 : ParNat := fun s g hg hh p => (gE0v3 selector mask packets rows s g hg hh p + 64)^3

def gC0v3 : ParNat := fun s g hg hh p =>
  gC0 selector packets s g hg hh p + PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP s) + reqC s p

/-- **The gauge coefficient v3.** -/
def gCv3 : ParNat := fun s g hg hh p => (gC0v3 selector packets s g hg hh p + 2)^(gEv3 selector mask packets rows s g hg hh p)

end gauge

section site


end site

/-! ## 3. The seam's reserve premises at `siteR3` (rounded `Vv' = VvOf2`), and census H2 at the gauge v3 -/

section fits
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g) (k : Nat)

theorem workspace_mono (printer : WilliamsAlgorithm) {V W : Nat} (h : V ≤ W) :
    P1TopDownPaidReusableReserves.workspace printer V ≤ P1TopDownPaidReusableReserves.workspace printer W := by
  unfold P1TopDownPaidReusableReserves.workspace
  exact Nat.mul_le_mul_left _ (by omega)

theorem rewind_mono (printer : WilliamsAlgorithm) {V W : Nat} (h : V ≤ W) :
    P1TopDownPaidReusableReserves.rewind printer V ≤ P1TopDownPaidReusableReserves.rewind printer W := by
  unfold P1TopDownPaidReusableReserves.rewind
  exact Nat.mul_le_mul_left _ (by omega)

/-- **Census H2 at the gauge v3**: the first seam's query-cache width `C = capacity (size + arity)` fits `gCv3·(q+1)^gEv3` at `q = widthAt`. -/
theorem queryCap_fit {n : Nat} (x : BitInput n) (bits : List Bool) :
    PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP s)
        ((req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
          (req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity) ≤
      gCv3 selector mask packets rows s g hg hh p * (C10PartsSchedule.widthAt s k n + 1) ^ gEv3 selector mask packets rows s g hg hh p := by
  have hs := req_size_le s k p x bits
  have hsh := shortAt_le s p (C10PartsSchedule.widthAt s k n)
  have hD1 : PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) ≤ gE0v3 selector mask packets rows s g hg hh p := by
    unfold gE0v3
    have : PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) ≤ (reqE s p + 1) * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hRD : reqE s p * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) ≤ gE0v3 selector mask packets rows s g hg hh p := by
    unfold gE0v3
    have : reqE s p * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) ≤ (reqE s p + 1) * PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hc : PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP s) ≤ gC0v3 selector packets s g hg hh p := by
    unfold gC0v3; omega
  have hrc : reqC s p ≤ gC0v3 selector packets s g hg hh p := by
    unfold gC0v3; omega
  show PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP s) *
      ((req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
        (req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity + 1) ^
        PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) ≤
    (gC0v3 selector packets s g hg hh p + 2) ^ ((gE0v3 selector mask packets rows s g hg hh p + 64) ^ 3) *
      (C10PartsSchedule.widthAt s k n + 1) ^ ((gE0v3 selector mask packets rows s g hg hh p + 64) ^ 3)
  generalize (req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size +
    (req s k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf s k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity = N at hs ⊢
  generalize C10PartsSchedule.widthAt s k n = q at hsh hs ⊢
  generalize shortAt s p q = sh at hsh hs
  generalize PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP s) = D at hD1 hRD ⊢
  generalize PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP s) = c at hc ⊢
  generalize reqE s p = R at hsh hRD
  generalize reqC s p = rc at hsh hrc
  generalize gC0v3 selector packets s g hg hh p = x0 at hc hrc ⊢
  generalize gE0v3 selector mask packets rows s g hg hh p = X at hD1 hRD ⊢
  have hq1 : 1 ≤ (q+1)^R := Nat.one_le_pow _ _ (by omega)
  have hA : rc * (q+1)^R ≤ x0 * (q+1)^R := Nat.mul_le_mul_right _ hrc
  have hN1 : N + 1 ≤ (2*rc + 1)*(q+1)^R := by
    have e1 : (2*rc + 1)*(q+1)^R = 2*(rc*(q+1)^R) + (q+1)^R := by ring
    rw [e1]
    omega
  have hpow : (N+1)^D ≤ (2*rc + 1)^D * (q+1)^(R*D) := by
    calc (N+1)^D ≤ ((2*rc + 1)*(q+1)^R)^D := Nat.pow_le_pow_left hN1 D
      _ = (2*rc + 1)^D * (q+1)^(R*D) := by rw [mul_pow, ← pow_mul]
  have hX2 : 2 * (X + 64) ≤ (X + 64) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  have hX3 : (X + 64) ^ 2 ≤ (X + 64) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hX1 : X + 64 ≤ (X + 64) ^ 3 := Nat.le_self_pow (by decide) _
  have hE2 : 2*D + 1 ≤ (X + 64) ^ 3 := by omega
  have hbase : 2*rc + 1 ≤ (x0 + 2)^2 := by
    have : 2 * (x0 + 2) ≤ (x0 + 2) * (x0 + 2) := Nat.mul_le_mul_right _ (by omega)
    rw [pow_two]
    omega
  have hcoef : c * (2*rc + 1)^D ≤ (x0 + 2)^((X + 64) ^ 3) := by
    calc c * (2*rc + 1)^D ≤ (x0 + 2) * ((x0 + 2)^2)^D := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hbase D)
      _ = (x0 + 2)^(2*D + 1) := by rw [← pow_mul, pow_succ, Nat.mul_comm]
      _ ≤ (x0 + 2)^((X + 64) ^ 3) := Nat.pow_le_pow_right (by omega) hE2
  have hexp : (q+1)^(R*D) ≤ (q+1)^((X + 64) ^ 3) := Nat.pow_le_pow_right (by omega) (by omega)
  calc c * (N+1)^D ≤ c * ((2*rc + 1)^D * (q+1)^(R*D)) := Nat.mul_le_mul_left _ hpow
    _ = (c * (2*rc + 1)^D) * (q+1)^(R*D) := by ring
    _ ≤ (x0 + 2)^((X + 64) ^ 3) * (q+1)^((X + 64) ^ 3) := Nat.mul_le_mul hcoef hexp

end fits

end
end NearCubicWires.SourceSkeleton.ClassV3
end

