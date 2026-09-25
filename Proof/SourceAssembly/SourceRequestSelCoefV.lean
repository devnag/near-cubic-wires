import Proof.Assembly.CappedCoordinate
import Proof.CaseAnalysis.FinalModeNativeSchedule

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelCoefV
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
noncomputable section

section any
variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) {n : Nat} (x : BitInput n) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)) (bits : List Bool)

/-- The capped decoder's coefficient-bit cap. -/
abbrev capOf : Nat := (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap

/-- **Every coordinate coefficient fits the cap** (both branches). -/
theorem coord_fits (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    C10SiteCoefficientsFit.PolynomialFits (capOf sources k clock p den x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j]
    exact C10SumFamilyTransport.polynomialFits_map_familyCoordinate _ rfl _ j
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j]
    have ht : (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).coefficientBitCap =
        (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap := rfl
    show C10SiteCoefficientsFit.PolynomialFits
      (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap _
    rw [← ht]
    exact C10SumFamilyTransport.polynomialFits_map_familyCoordinate _ rfl _ j

/-- **`hcoefV`** for any value bound above `2^capOf`. -/
theorem hcoefV_of_lt (Vb : Nat) (hVb : 2 ^ capOf sources k clock p den x oracle < Vb) :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials,
      mo.coefficient.num.natAbs < Vb ∧ mo.coefficient.den < Vb := by
  intro j mo hmo
  obtain ⟨h1, h2⟩ := coord_fits sources k clock p den x oracle bits j mo hmo
  exact ⟨lt_of_le_of_lt h1 hVb, lt_of_le_of_lt h2 hVb⟩

/-- **`hcoef`** for any width above `capOf`. -/
theorem hcoef_of_lt (cw : Nat) (hcw : capOf sources k clock p den x oracle < cw) :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).monomials,
      mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw :=
  hcoefV_of_lt sources k clock p den x oracle bits (2 ^ cw) (Nat.pow_lt_pow_right (by decide) hcw)

end any

section site
variable (sources : EightSources) (k : Nat) {gamma : Real} (p : Parameters sources gamma) (den n : Nat) (x : BitInput n) (bits : List Bool)

theorem cap_le_floor :
    capOf sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ≤
      CloseoutFinalC10ClauseBitsUniform.coefficientBitFloor sources k p n :=
  CloseoutFinalC10ClauseBitsUniform.coefficientBitCap_le sources k p n x bits

/-- The floor is below the coefficient width at the native arity. -/
theorem floor_lt_coefficientAt :
    CloseoutFinalC10ClauseBitsUniform.coefficientBitFloor sources k p n <
      CloseoutFinalC10ModeNativeSchedule.coefficientAt sources p (NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k n) := by
  rw [CloseoutFinalC10ModeNativeSchedule.coefficientAt_eq]
  unfold CloseoutFinalC10ClauseBitsUniform.coefficientFloor
  omega

/-- **The site-uniform value bound** (depends on `n` only). -/
def VbF : Nat := 2 ^ CloseoutFinalC10ClauseBitsUniform.coefficientBitFloor sources k p n + 4

theorem four_le_VbF : 4 ≤ VbF sources k p n := Nat.le_add_left 4 _

theorem hcoefV_site :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits j).monomials,
      mo.coefficient.num.natAbs < VbF sources k p n ∧ mo.coefficient.den < VbF sources k p n := by
  apply hcoefV_of_lt
  have h := cap_le_floor sources k p den n x bits
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  unfold VbF
  omega

theorem hcoef_site (cw : Nat)
    (hcw : CloseoutFinalC10ModeNativeSchedule.coefficientAt sources p (NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k n) ≤ cw) :
    ∀ j, ∀ mo ∈ (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits j).monomials,
      mo.coefficient.num.natAbs < 2 ^ cw ∧ mo.coefficient.den < 2 ^ cw := by
  apply hcoef_of_lt
  have h1 := cap_le_floor sources k p den n x bits
  have h2 := floor_lt_coefficientAt sources k p n
  omega

/-- `2^natBitLength v ≤ 2·max 1 v`. -/
theorem pow_natBitLength_le (v : Nat) : 2 ^ natBitLength v ≤ 2 * max 1 v := by
  unfold natBitLength
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos v with h0 | h0
  · subst h0; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h0)
    have hm : v ≤ max 1 v := le_max_right _ _
    omega

theorem VbF_le :
    VbF sources k p n ≤ 2 * max 1 (CloseoutXor.cap (CompetitorRationalGap.zeta (constantsOf sources))
        (CloseoutFinalC10ClauseBitsUniform.sampleArity sources k p n) p.copies
      * max 1 (2 * CloseoutFinalC10ClauseBitsUniform.clauseCap sources k p.degree n)) + 4 := by
  unfold VbF CloseoutFinalC10ClauseBitsUniform.coefficientBitFloor
  have := pow_natBitLength_le (CloseoutXor.cap (CompetitorRationalGap.zeta (constantsOf sources))
      (CloseoutFinalC10ClauseBitsUniform.sampleArity sources k p n) p.copies
    * max 1 (2 * CloseoutFinalC10ClauseBitsUniform.clauseCap sources k p.degree n))
  omega

end site

end
end NearCubicWires.SourceRequest.SelCoefV

