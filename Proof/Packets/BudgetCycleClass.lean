import Proof.SourceAssembly.AdmissionPhase
import Proof.SourceAssembly.SourcePhaseFuel

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator

noncomputable section

/-! ## 1. The uniform capacity `V` and the three reserves -/

/-- The workspace reserve `(2·coef+20)(V+1)` in the classes, from `V`'s class. -/
theorem workspace_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*(cP+1))
      ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cT)
      ((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cS)
      (P1TopDownPaidReusableReserves.workspace printer V) := by
  unfold P1TopDownPaidReusableReserves.workspace
  exact (hV.add_const 1).smul _

/-- The rewind reserve `(coef+2)(V+1)`. -/
theorem rewind_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn ((P1TopDownPaidReusableReserves.coefficient printer+2)*(cP+1))
      ((P1TopDownPaidReusableReserves.coefficient printer+2)*cT)
      ((P1TopDownPaidReusableReserves.coefficient printer+2)*cS)
      (P1TopDownPaidReusableReserves.rewind printer V) := by
  unfold P1TopDownPaidReusableReserves.rewind
  exact (hV.add_const 1).smul _

/-- The buffer reserve `V+1`. -/
theorem buffer_inClasses {dP hT hS m L n qn cP cT cS V : ℕ}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) :
    InClasses dP hT hS m L n qn (cP+1) cT cS (P1TopDownPaidReusableReserves.buffer V) := by
  unfold P1TopDownPaidReusableReserves.buffer
  exact hV.add_const 1

/-! ## 2. Polynomial bookkeeping -/

/-- Products and sums of two `n`-polynomial quantities under one monomial. -/
theorem poly_mul {a b A B e f n : ℕ} (ha : a ≤ A*(n+1)^e) (hb : b ≤ B*(n+1)^f) :
    a*b ≤ (A*B)*(n+1)^(e+f) := by
  calc a*b ≤ (A*(n+1)^e)*(B*(n+1)^f) := Nat.mul_le_mul ha hb
    _ = (A*B)*(n+1)^(e+f) := by rw [pow_add]; ring

theorem poly_raise {a A e E n : ℕ} (ha : a ≤ A*(n+1)^e) (h : e ≤ E) : a ≤ A*(n+1)^E :=
  ha.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h))

theorem le_box_x (nC xC : ℕ) : xC ≤ (nC+1)*(xC+1)*(xC+1) := by
  have h1 : 1 ≤ (nC+1)*(xC+1) := Nat.mul_pos (by omega) (by omega)
  have h2 : xC+1 ≤ (nC+1)*(xC+1)*(xC+1) := Nat.le_mul_of_pos_left _ h1
  omega

theorem le_box_n (nC xC : ℕ) : nC ≤ (nC+1)*(xC+1)*(xC+1) := by
  have h1 : 1 ≤ (xC+1)*(xC+1) := Nat.mul_pos (by omega) (by omega)
  have h2 : nC+1 ≤ (nC+1)*((xC+1)*(xC+1)) := Nat.le_mul_of_pos_right _ h1
  rw [← Nat.mul_assoc] at h2
  omega

theorem le_box_nx (nC xC : ℕ) : nC*xC ≤ (nC+1)*(xC+1)*(xC+1) := by
  have h1 : nC*xC ≤ (nC+1)*(xC+1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (nC+1)*(xC+1) ≤ (nC+1)*(xC+1)*(xC+1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem le_box_xx (nC xC : ℕ) : xC*xC ≤ (nC+1)*(xC+1)*(xC+1) := by
  have h1 : xC*xC ≤ (xC+1)*(xC+1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (xC+1)*(xC+1) ≤ (nC+1)*((xC+1)*(xC+1)) := Nat.le_mul_of_pos_left _ (by omega)
  rw [← Nat.mul_assoc] at h2
  omega

/-! ## 3. The per-entry family fuel (`SourceTrace`'s `familyCost` bound) -/

/-- The per-entry family fuel of `SourceTrace` (`Proof/CaseAnalysis/FiveSourceTrace.lean`), verbatim. -/
def familyEntryFuel (printer : WilliamsAlgorithm) (S rowWidth b N D cnt : ℕ) : ℕ :=
  PCJ1fef9807c6954e94_Native.f_budget printer S rowWidth b N + 1 +
    (2*D+4+1+(2*PCJ1fef9807c6954e94_Native.e_emitCost b+2)+1+CloseoutFinalC10AppendPositioning.budget b cnt)

/-- **The family entry in the classes.** The workspace `S` (table + small) is multiplied only by the row count
`N` (a `q`-polynomial count); every other summand is source-polynomial in the row width, the record width, the
payload length `D` and the record count. -/
theorem familyEntry_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn cP cT cS : ℕ}
    (S rowWidth b N D cnt nC nE xC xE : ℕ)
    (hNn : N ≤ nC*(n+1)^nE) (hNq : N ≤ nC*(qn+1)^nE)
    (hSp : InClasses dP hT hS m L n qn cP cT cS S)
    (hx : rowWidth + b + D + cnt + 1 ≤ xC*(n+1)^xE)
    (hdP : nE + (xE + xE) ≤ dP) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn
      ((3*P1TopDownPaidPayload.tapes printer+6)*(nC*cP) +
        (3*P1TopDownPaidPayload.tapes printer + 700)*((nC+1)*(xC+1)*(xC+1)))
      ((3*P1TopDownPaidPayload.tapes printer+6)*(nC*cT)) ((3*P1TopDownPaidPayload.tapes printer+6)*(nC*cS))
      (familyEntryFuel printer S rowWidth b N D cnt) := by
  set T := P1TopDownPaidPayload.tapes printer with hTdef
  -- the table part: `N·S`
  have hNS := (hSp.count2 hNn hNq).smul (3*T+6)
  -- the polynomial part, under `Z := (nC+1)(xC+1)^2 (n+1)^(nE+2xE)`
  set Z := ((nC+1)*(xC+1)*(xC+1))*(n+1)^(nE+(xE+xE)) with hZ
  have hX : xC*(n+1)^xE ≤ Z := by
    have h1 : xC*(n+1)^xE ≤ xC*(n+1)^(nE+(xE+xE)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : xC ≤ (nC+1)*(xC+1)*(xC+1) := le_box_x nC xC
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hN : nC*(n+1)^nE ≤ Z := by
    have h1 : nC*(n+1)^nE ≤ nC*(n+1)^(nE+(xE+xE)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : nC ≤ (nC+1)*(xC+1)*(xC+1) := le_box_n nC xC
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hNX : (nC*(n+1)^nE)*(xC*(n+1)^xE) ≤ Z := by
    have e : (nC*(n+1)^nE)*(xC*(n+1)^xE) = (nC*xC)*(n+1)^(nE+xE) := by rw [pow_add]; ring
    rw [e]
    have h1 : (nC*xC)*(n+1)^(nE+xE) ≤ (nC*xC)*(n+1)^(nE+(xE+xE)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : nC*xC ≤ (nC+1)*(xC+1)*(xC+1) := le_box_nx nC xC
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hXX : (xC*(n+1)^xE)*(xC*(n+1)^xE) ≤ Z := by
    have e : (xC*(n+1)^xE)*(xC*(n+1)^xE) = (xC*xC)*(n+1)^(xE+xE) := by rw [pow_add]; ring
    rw [e]
    have h1 : (xC*xC)*(n+1)^(xE+xE) ≤ (xC*xC)*(n+1)^(nE+(xE+xE)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : xC*xC ≤ (nC+1)*(xC+1)*(xC+1) := le_box_xx nC xC
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hZ1 : 1 ≤ Z := by
    have h1 : 1 ≤ (n+1)^(nE+(xE+xE)) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ (nC+1)*(xC+1)*(xC+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    exact Nat.mul_pos h2 h1
  -- the individual products
  have hw : rowWidth ≤ xC*(n+1)^xE := by omega
  have hb : b ≤ xC*(n+1)^xE := by omega
  have hD : D ≤ xC*(n+1)^xE := by omega
  have hc : cnt ≤ xC*(n+1)^xE := by omega
  have p1 : N*rowWidth ≤ (nC*(n+1)^nE)*(xC*(n+1)^xE) := Nat.mul_le_mul hNn hw
  have p2 : N*b ≤ (nC*(n+1)^nE)*(xC*(n+1)^xE) := Nat.mul_le_mul hNn hb
  have p3 : cnt*b ≤ (xC*(n+1)^xE)*(xC*(n+1)^xE) := Nat.mul_le_mul hc hb
  have poly : 2*(N*rowWidth) + 2 + 1 + (2*(N*(16*b+20)+5)+2) + (3*T+9)*N + 3 + 1 + 1 +
      (2*D+4+1+(2*(40*b+56)+2)+1+(80*cnt*b+110*cnt+160*b+256)) ≤
      (3*T + 700)*((nC+1)*(xC+1)*(xC+1))*(n+1)^(nE+(xE+xE)) := by
    have e1 : N*(16*b+20) = 16*(N*b) + 20*N := by ring
    have e2 : 80*cnt*b = 80*(cnt*b) := by ring
    have e3 : (3*T + 700)*((nC+1)*(xC+1)*(xC+1))*(n+1)^(nE+(xE+xE)) = (3*T + 700)*Z := by
      rw [hZ]; ring
    rw [e1, e2, e3]
    have hNZ : N ≤ Z := hNn.trans hN
    have hTN : (3*T+9)*N ≤ (3*T+9)*Z := Nat.mul_le_mul_left _ hNZ
    have e4 : (3*T + 700)*Z = (3*T+9)*Z + 691*Z := by ring
    rw [e4]
    omega
  have hpoly : InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn
      ((3*T + 700)*((nC+1)*(xC+1)*(xC+1))) 0 0
      (2*(N*rowWidth) + 2 + 1 + (2*(N*(16*b+20)+5)+2) + (3*T+9)*N + 3 + 1 + 1 +
        (2*D+4+1+(2*(40*b+56)+2)+1+(80*cnt*b+110*cnt+160*b+256))) :=
    InClasses.poly poly (by omega)
  have hsum := hNS.add hpoly
  refine InClasses.mono ?_ (hsum.coeff_mono le_rfl (by simp) (by simp))
  unfold familyEntryFuel PCJ1fef9807c6954e94_Native.f_budget RepairSource.CloseoutFinal.C10ExternalRowLoop.familyFuel
    P1TopDownPaidFamilySum.budget CloseoutFinalC10RowAnswerWord.rowAnswerFuel PCJ1fef9807c6954e94_Native.e_emitCost
  rw [CloseoutFinalC10AppendPositioning.budget_eq]
  have e5 : N*((3*T+6)*(S+1)+3) = (3*T+6)*(N*S) + (3*T+9)*N := by ring
  rw [← hTdef, e5]
  omega

/-! ## 4. The row family (`cycFuel`'s `Family.budget` summand) -/

/-- **The row family in the classes.** `|rows|·(rowFuel+3)+3` with `rowFuel ≤ rowBudget` in the classes and
the row count `q`-polynomial (`paper.tex:1203-1207`: the rows multiply the one-row charges once). -/
theorem familyBudget_inClasses {printer : WilliamsAlgorithm} {t : ℕ} {q L : ℕ} (F : PCJ9eff70d512234a4c_Fixed.Packets.Family q L)
    (s : PCJ38fbfed565f64139_Family.State (t := t) printer)
    {dP hT hS m L' n qn cP cT cS rb nC nE : ℕ}
    (hrow : s.rowFuel ≤ rb) (hrb : InClasses dP hT hS m L' n qn cP cT cS rb)
    (hNn : F.rows.length ≤ nC*(n+1)^nE) (hNq : F.rows.length ≤ nC*(qn+1)^nE) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L' n qn (nC*(cP+3) + 3) (nC*cT) (nC*cS)
      (PCJ38fbfed565f64139_Family.budget printer F s) := by
  unfold PCJ38fbfed565f64139_Family.budget
  rw [List.length_attach]
  have h1 := ((hrb.add_const 3).count2 hNn hNq).add_const 3
  refine InClasses.mono ?_ (h1.raise le_rfl le_rfl le_rfl)
  have := Nat.mul_le_mul_left F.rows.length (Nat.add_le_add_right hrow 3)
  omega

end
end NearCubicWires.SourceBudget

