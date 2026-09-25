import Proof.SourceAssembly.AdmissionSmall

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierEstimator NearCubicWires.RuntimeShape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces

noncomputable section

/-- The `Split.bound` right-hand side at one input length `n` and width `qn`. -/
def splitRHS (dP hT hS m L cP cT cS n qn : ℕ) : ℕ :=
  cP*(n+1)^dP + cT*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) + cS*((qn+1)^hS*2^(qn/m))

/-- `x` lies in the three paper classes with coefficients `(cP, cT, cS)`. -/
def InClasses (dP hT hS m L n qn cP cT cS x : ℕ) : Prop :=
  x ≤ splitRHS dP hT hS m L cP cT cS n qn

section
variable {dP hT hS m L n qn : ℕ}

theorem InClasses.mono {cP cT cS x y : ℕ} (hxy : x ≤ y)
    (hy : InClasses dP hT hS m L n qn cP cT cS y) : InClasses dP hT hS m L n qn cP cT cS x :=
  hxy.trans hy

theorem InClasses.add {cP cT cS cP' cT' cS' x y : ℕ}
    (hx : InClasses dP hT hS m L n qn cP cT cS x) (hy : InClasses dP hT hS m L n qn cP' cT' cS' y) :
    InClasses dP hT hS m L n qn (cP+cP') (cT+cT') (cS+cS') (x+y) := by
  unfold InClasses splitRHS at *
  have e : (cP+cP')*(n+1)^dP + (cT+cT')*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
      (cS+cS')*((qn+1)^hS*2^(qn/m)) =
      (cP*(n+1)^dP + cT*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) + cS*((qn+1)^hS*2^(qn/m))) +
      (cP'*(n+1)^dP + cT'*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
        cS'*((qn+1)^hS*2^(qn/m))) := by ring
  rw [e]
  omega

theorem InClasses.coeff_mono {cP cT cS cP' cT' cS' x : ℕ} (hP : cP ≤ cP') (hT' : cT ≤ cT')
    (hS' : cS ≤ cS') (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses dP hT hS m L n qn cP' cT' cS' x := by
  unfold InClasses splitRHS at *
  have h1 := Nat.mul_le_mul_right ((n+1)^dP) hP
  have h2 := Nat.mul_le_mul_right ((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) hT'
  have h3 := Nat.mul_le_mul_right ((qn+1)^hS*2^(qn/m)) hS'
  omega

theorem InClasses.const (c : ℕ) : InClasses dP hT hS m L n qn c 0 0 c := by
  unfold InClasses splitRHS
  have : c ≤ c*(n+1)^dP := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (Nat.succ_pos n))
  omega

theorem InClasses.zero : InClasses dP hT hS m L n qn 0 0 0 0 := by
  unfold InClasses splitRHS
  omega

theorem InClasses.smul (k : ℕ) {cP cT cS x : ℕ} (hx : InClasses dP hT hS m L n qn cP cT cS x) :
    InClasses dP hT hS m L n qn (k*cP) (k*cT) (k*cS) (k*x) := by
  unfold InClasses splitRHS at *
  have h := Nat.mul_le_mul_left k hx
  have e : k*(cP*(n+1)^dP + cT*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
      cS*((qn+1)^hS*2^(qn/m))) =
      k*cP*(n+1)^dP + k*cT*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
      k*cS*((qn+1)^hS*2^(qn/m)) := by ring
  omega

/-- Raising any exponent keeps a quantity in the classes. -/
theorem InClasses.raise {dP' hT' hS' cP cT cS x : ℕ} (hd : dP ≤ dP') (ht : hT ≤ hT') (hs : hS ≤ hS')
    (hx : InClasses dP hT hS m L n qn cP cT cS x) : InClasses dP' hT' hS' m L n qn cP cT cS x := by
  unfold InClasses splitRHS at *
  have h1 := Nat.mul_le_mul_left cP (Nat.pow_le_pow_right (by omega : 0 < n+1) hd)
  have h2 := Nat.mul_le_mul_left cT (Nat.mul_le_mul_right (2^(qn - normalizedLiveCount qn L))
    (Nat.pow_le_pow_right (by omega : 0 < qn+1) ht))
  have h3 := Nat.mul_le_mul_left cS (Nat.mul_le_mul_right (2^(qn/m))
    (Nat.pow_le_pow_right (by omega : 0 < qn+1) hs))
  omega

theorem InClasses.table {cT x : ℕ} (hx : x ≤ cT*tableClass L hT qn) :
    InClasses dP hT hS m L n qn 0 cT 0 x := by
  unfold InClasses splitRHS
  unfold tableClass at hx
  omega

theorem InClasses.small {cS x : ℕ} (hx : x ≤ cS*smallClass m hS qn) :
    InClasses dP hT hS m L n qn 0 0 cS x := by
  unfold InClasses splitRHS
  unfold smallClass at hx
  omega

theorem InClasses.table_small {cT cS x : ℕ}
    (hx : x ≤ cT*tableClass L hT qn + cS*smallClass m hS qn) :
    InClasses dP hT hS m L n qn 0 cT cS x := by
  unfold InClasses splitRHS
  unfold tableClass smallClass at hx
  omega

end

/-! ## Producer budgets in class form -/

/-- A row call, from `rowBudget_classes` and the admission facts. -/
theorem rowBudget_inClasses (a : DecompositionAlgorithm) (c d : ℕ) (r : Request) (C : ℕ)
    (caps : RowCaps) (m inputC inputE smallC smallE headerC headerE capC capE
      copyTC copyTE copySC copySE dP n : ℕ)
    (h_input : (r.input a).length ≤ inputC*(r.q+1)^inputE)
    (h_small : (r.smallSize a)^d ≤ smallC*smallClass m smallE r.q)
    (h_header : caps.headerFuel ≤ headerC*smallClass m headerE r.q)
    (h_cap : C ≤ capC*smallClass m capE r.q)
    (h_copy : caps.copyCap ≤
      copyTC*tableClass r.liveScale copyTE r.q+copySC*smallClass m copySE r.q) :
    InClasses dP ((inputE+1)*d+copyTE) (smallE+headerE+capE+copySE) m r.liveScale n r.q
      0 (c*((inputC+2)^d+copyTC)) (c*(smallC+headerC+capC+copySC+1)) (rowBudget a c d r C caps) :=
  InClasses.table_small (rowBudget_classes a c d r C caps m inputC inputE smallC smallE headerC headerE
    capC capE copyTC copyTE copySC copySE h_input h_small h_header h_cap h_copy)

/-- A packet call, from `packetBudget_classes`. -/
theorem packetBudget_inClasses (a : DecompositionAlgorithm) (c d : ℕ) (r : Request)
    (m rowsC rowsE smallC smallE dP hT n : ℕ)
    (h_rows : (r.family a).rows.length+1 ≤ rowsC*(r.q+1)^rowsE)
    (h_small : (r.smallSize a)^d ≤ smallC*smallClass m smallE r.q) :
    InClasses dP hT (rowsE+smallE) m r.liveScale n r.q 0 0 (c*rowsC*smallC) (packetBudget a c d r) :=
  InClasses.small (packetBudget_classes a c d r m rowsC rowsE smallC smallE h_rows h_small)

/-! ## J5 -/

/-- **J5.** If each phase's cost lies in the classes and the tail verdict budget is source-polynomial,
the branch fuel plus two lies under `splitRHS` with the phase coefficients summed. -/
theorem branchFuel_le_split (cost width : Phase → ℕ) (dP hT hS m L n qn cP cT cS cW : ℕ)
    (hphase : ∀ ph, InClasses dP hT hS m L n qn cP cT cS (cost ph))
    (htail : C10TailVerdictUniform.tbud (max (width .penalty) (max (width .moment) (width .clause))) + 5 ≤
      cW*(n+1)^dP) :
    PCJ374c44bb8b7f47d9_.branchFuel cost width + 2 ≤
      splitRHS dP hT hS m L (3*cP+cW) (3*cT) (3*cS) n qn := by
  have h3 := ((hphase .penalty).add (hphase .moment)).add (hphase .clause)
  unfold InClasses splitRHS at h3
  unfold PCJ374c44bb8b7f47d9_.branchFuel splitRHS
  have e : (3*cP+cW)*(n+1)^dP + 3*cT*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
      3*cS*((qn+1)^hS*2^(qn/m)) =
      ((cP+cP+cP)*(n+1)^dP + (cT+cT+cT)*((qn+1)^hT*2^(qn - normalizedLiveCount qn L)) +
        (cS+cS+cS)*((qn+1)^hS*2^(qn/m))) + cW*(n+1)^dP := by ring
  rw [e]
  omega

/-! ## Counts: calls per clause (`h_calls`) and clauses (`h_clauses`) -/

theorem calls_poly {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (ph : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (address : Fin (2^pcpp.clauseBits))
    (T tC tE q : ℕ) (hT : T ≤ tC*(q+1)^tE) (hL : ∀ i, (coordinate i).monomials.length ≤ T) :
    (RepairOrdinary.CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate systematicAtom
      address).monomials.length ≤ (16*(tC+1)^4)*(q+1)^(4*tE) := by
  unfold RepairOrdinary.CloseoutFinalC10SupplierCalls.siteCalls
  rw [RepairOrdinary.CloseoutFinalC10CallCountCap.scale_length]
  refine (RepairOrdinary.CloseoutFinalC10CallCountCap.site_le T arity pcpp ph coordinate systematicAtom
    hL address).trans ?_
  unfold RepairOrdinary.CloseoutFinalC10CallCountCap.siteCap
  have h1 : T + 1 ≤ (tC+1)*(q+1)^tE := by
    have : 1 ≤ (q+1)^tE := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc 16*(T+1)^4 ≤ 16*((tC+1)*(q+1)^tE)^4 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left h1 4)
    _ = (16*(tC+1)^4)*(q+1)^(4*tE) := by rw [mul_pow, ← pow_mul, Nat.mul_comm tE 4]; ring


end
end NearCubicWires.Admission
