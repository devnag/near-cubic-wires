import Proof.SourceAssembly.AdmissionRuntime

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal

noncomputable section

section
variable {dP hT hS m L n qn : ℕ}

/-- **Multiplicities, two-sided**: a count bounded polynomially in both `n` and `qn` multiplies a class
quantity into the classes (no relation between `n` and `qn` needed). -/
theorem InClasses.count2 {cP cT cS x N nC nE : ℕ} (hNn : N ≤ nC*(n+1)^nE) (hNq : N ≤ nC*(qn+1)^nE)
    (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn (nC*cP) (nC*cT) (nC*cS) (N*x) := by
  unfold InClasses splitRHS at *
  set T := 2^(qn - normalizedLiveCount qn L)
  set S := 2^(qn/m)
  have h1 : N*(cP*(n+1)^dP) ≤ nC*cP*(n+1)^(nE+dP) := by
    calc N*(cP*(n+1)^dP) ≤ nC*(n+1)^nE*(cP*(n+1)^dP) := Nat.mul_le_mul_right _ hNn
      _ = nC*cP*(n+1)^(nE+dP) := by rw [pow_add]; ring
  have h2 : N*(cT*((qn+1)^hT*T)) ≤ nC*cT*((qn+1)^(nE+hT)*T) := by
    calc N*(cT*((qn+1)^hT*T)) ≤ nC*(qn+1)^nE*(cT*((qn+1)^hT*T)) := Nat.mul_le_mul_right _ hNq
      _ = nC*cT*((qn+1)^(nE+hT)*T) := by rw [pow_add]; ring
  have h3 : N*(cS*((qn+1)^hS*S)) ≤ nC*cS*((qn+1)^(nE+hS)*S) := by
    calc N*(cS*((qn+1)^hS*S)) ≤ nC*(qn+1)^nE*(cS*((qn+1)^hS*S)) := Nat.mul_le_mul_right _ hNq
      _ = nC*cS*((qn+1)^(nE+hS)*S) := by rw [pow_add]; ring
  have hm := Nat.mul_le_mul_left N hx
  have e : N*(cP*(n+1)^dP + cT*((qn+1)^hT*T) + cS*((qn+1)^hS*S)) =
      N*(cP*(n+1)^dP) + N*(cT*((qn+1)^hT*T)) + N*(cS*((qn+1)^hS*S)) := by ring
  omega

/-- A constant `c` added to a class quantity. -/
theorem InClasses.add_const {cP cT cS x : ℕ} (c : ℕ) (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses dP hT hS m L n qn (cP+c) cT cS (x+c) := by
  have h := hx.add (InClasses.const (dP := dP) (hT := hT) (hS := hS) (m := m) (L := L) (n := n)
    (qn := qn) c)
  simpa using h

/-- A polynomial count (in `n`) at an exponent `≤ dP` is source-polynomial. -/
theorem InClasses.poly {x c e : ℕ} (hx : x ≤ c*(n+1)^e) (he : e ≤ dP) :
    InClasses dP hT hS m L n qn c 0 0 x := by
  unfold InClasses splitRHS
  have := Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega : 0 < n+1) he)
  omega

end

/-! ## Per clause: `SourceTrace.budget` -/

/-- **The per-clause site fuel** (`SourceTrace.budget`'s left side) is in the classes, from class bounds on
the first call, the family machine and the refill, and a polynomial call count `E` (`calls_poly`). -/
theorem siteFuel_inClasses {dP hT hS m L n qn cP cT cS E eC eE firstCost familyCost refillCost : ℕ}
    (hEn : E ≤ eC*(n+1)^eE) (hEq : E ≤ eC*(qn+1)^eE)
    (hFirst : InClasses dP hT hS m L n qn cP cT cS firstCost)
    (hFam : InClasses dP hT hS m L n qn cP cT cS familyCost)
    (hRef : InClasses dP hT hS m L n qn cP cT cS refillCost) :
    InClasses (eE+dP) (eE+hT) (eE+hS) m L n qn
      (cP + eC*(cP+cP+4) + 4) (cT + eC*(cT+cT)) (cS + eC*(cS+cS))
      (firstCost+1+(E*(familyCost+1+refillCost+3)+3)) := by
  have h1 : InClasses dP hT hS m L n qn (cP+cP+4) (cT+cT) (cS+cS) (familyCost+1+refillCost+3) := by
    have h := (hFam.add hRef).add_const 4
    exact h.mono (by omega)
  have h2 := h1.count2 hEn hEq
  have h3 := hFirst.raise (dP' := eE+dP) (hT' := eE+hT) (hS' := eE+hS) (by omega) (by omega) (by omega)
  have h4 := (h3.add h2).add_const 4
  refine (h4.mono (le_of_eq (by ring))).coeff_mono (by ring_nf; omega) (by ring_nf; omega)
    (by ring_nf; omega)

/-! ## Per phase: `MaskedPhase`'s fuel -/

/-- **The phase fuel** (`MaskedPhase`'s `fuel` at `cost := 4N + callBudget + siteFuel + 21`) is in the
classes, from class bounds on the entry, the PCPP query term, the site fuel and the fold, and a
polynomial clause count `N` (`clauses_poly`) at an exponent `nE ≤ dP`. -/
theorem phaseFuel_inClasses {dP hT hS m L n qn cP cT cS N nC nE entryFuel callB siteFuel foldFuel : ℕ}
    (hNn : N ≤ nC*(n+1)^nE) (hNq : N ≤ nC*(qn+1)^nE) (hnd : nE ≤ dP)
    (hEntry : InClasses dP hT hS m L n qn cP cT cS entryFuel)
    (hCall : InClasses dP hT hS m L n qn cP cT cS callB)
    (hSite : InClasses dP hT hS m L n qn cP cT cS siteFuel)
    (hFold : InClasses dP hT hS m L n qn cP cT cS foldFuel) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn
      (cP + nC*(cP+cP+4*nC+24) + cP + 5) (cT + nC*(cT+cT) + cT) (cS + nC*(cS+cS) + cS)
      (entryFuel+1+(N*((4*N+callB+siteFuel+21)+3)+3+1+foldFuel)) := by
  have h4N : InClasses dP hT hS m L n qn (4*nC) 0 0 (4*N) :=
    InClasses.poly (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 4 hNn) hnd
  have hcost : InClasses dP hT hS m L n qn (cP+cP+4*nC+24) (cT+cT) (cS+cS)
      ((4*N+callB+siteFuel+21)+3) := by
    have h := ((h4N.add hCall).add hSite).add_const 24
    exact (h.mono (by omega)).coeff_mono (by omega) (by omega) (by omega)
  have hcnt := hcost.count2 hNn hNq
  have he := hEntry.raise (dP' := nE+dP) (hT' := nE+hT) (hS' := nE+hS) (by omega) (by omega) (by omega)
  have hf := hFold.raise (dP' := nE+dP) (hT' := nE+hT) (hS' := nE+hS) (by omega) (by omega) (by omega)
  have h := ((he.add hcnt).add hf).add_const 5
  exact (h.mono (by omega)).coeff_mono (by omega) (by omega) (by omega)

theorem callBudget_inClasses {dP hT hS m L n qn : ℕ} (a : RepairRepresentation.PointwisePCPPAlgorithm)
    (s sC sE : ℕ) (hs : s + 1 ≤ sC*(n+1)^sE)
    (hd : sE*RepairOrdinary.PCPPQueryCachedBounds.degree a ≤ dP) :
    InClasses dP hT hS m L n qn
      (4*RepairOrdinary.PCPPQueryCachedBounds.coefficient a*sC^RepairOrdinary.PCPPQueryCachedBounds.degree a + 7)
      0 0 (RepairOrdinary.PCPPQueryCachedBounds.callBudget a s) := by
  unfold RepairOrdinary.PCPPQueryCachedBounds.callBudget RepairOrdinary.PCPPQueryCachedBounds.capacity
  set D := RepairOrdinary.PCPPQueryCachedBounds.degree a
  set c := RepairOrdinary.PCPPQueryCachedBounds.coefficient a
  have h1 : (s+1)^D ≤ sC^D*(n+1)^(sE*D) := by
    calc (s+1)^D ≤ (sC*(n+1)^sE)^D := Nat.pow_le_pow_left hs D
      _ = sC^D*(n+1)^(sE*D) := by rw [mul_pow, ← pow_mul]
  have h2 : (n+1)^(sE*D) ≤ (n+1)^dP := Nat.pow_le_pow_right (by omega) hd
  have h3 : 1 ≤ (n+1)^dP := Nat.one_le_pow _ _ (by omega)
  have h4 : 4*c*(s+1)^D ≤ 4*c*sC^D*(n+1)^dP := by
    calc 4*c*(s+1)^D ≤ 4*c*(sC^D*(n+1)^(sE*D)) := Nat.mul_le_mul_left _ h1
      _ ≤ 4*c*(sC^D*(n+1)^dP) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = 4*c*sC^D*(n+1)^dP := by ring
  have h4' : 4*(c*(s+1)^D) ≤ 4*c*sC^D*(n+1)^dP := by rw [← Nat.mul_assoc]; exact h4
  have e : (4*c*sC^D + 7)*(n+1)^dP = 4*c*sC^D*(n+1)^dP + 7*(n+1)^dP := by ring
  unfold InClasses splitRHS
  simp only [Nat.zero_mul, Nat.add_zero]
  omega

/-! ## Per branch: J5 from the three phases -/

theorem tail_bound (W wC wE n : ℕ) (hW : W+1 ≤ wC*(n+1)^wE) :
    C10TailVerdictUniform.tbud W + 5 ≤ (1000000*wC^2+5)*(n+1)^(2*wE) := by
  have ht := C10PartsSchedule.tbud_le W
  have h2 : (W+1)^2 ≤ (wC*(n+1)^wE)^2 := Nat.pow_le_pow_left hW 2
  have e : (wC*(n+1)^wE)^2 = wC^2*(n+1)^(2*wE) := by rw [mul_pow, ← pow_mul, Nat.mul_comm wE 2]
  have h1 : 1 ≤ (n+1)^(2*wE) := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have : (1000000*wC^2+5)*(n+1)^(2*wE) = 1000000*(wC^2*(n+1)^(2*wE)) + 5*(n+1)^(2*wE) := by ring
  omega

/-- **J5, assembled**: three phase fuels in the classes and widths `≤ poly(n)` give the consumer's
`branchFuel … + 2 ≤ splitRHS …`. -/
theorem branchFuel_of_phases (fuel width : Phase → ℕ) (dP hT hS m L n qn cP cT cS wC wE : ℕ)
    (hph : ∀ ph, InClasses dP hT hS m L n qn cP cT cS (fuel ph))
    (hW : max (width .penalty) (max (width .moment) (width .clause)) + 1 ≤ wC*(n+1)^wE)
    (hwd : 2*wE ≤ dP) :
    PCJ374c44bb8b7f47d9_.branchFuel fuel width + 2 ≤
      splitRHS dP hT hS m L (3*cP + (1000000*wC^2+5)) (3*cT) (3*cS) n qn := by
  apply branchFuel_le_split fuel width dP hT hS m L n qn cP cT cS (1000000*wC^2+5) hph
  exact (tail_bound _ wC wE n hW).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < n+1) hwd))


end
end NearCubicWires.Admission
