import Proof.SourceAssembly.SourceFactorSelCoef

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefR
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires.SourceFactorSel.CoefReduce NearCubicWires.SourceFactorSel.CoefValue NearCubicWires.SourceFactorSel.Coef
noncomputable section

/-! ## Value -/

/-- The monomial's coefficient from the cursor's multiplier record and the four slots. -/
def coefOfR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℚ :=
  (1 / (K : ℚ)) * (rho * ∏ i, u (f i) (t i))

def RN0 (rho : ℚ) : ℕ := 1 * rho.num.natAbs
def RD0 (rho : ℚ) : ℕ := 1 * rho.den
def RS0 (rho : ℚ) : ℕ := 0 + (decide (rho.num < 0)).toNat
def RN1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN0 rho * nA (f 0) (t 0)
def RN2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN1 rho f t * nA (f 1) (t 1)
def RN3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN2 rho f t * nA (f 2) (t 2)
def numR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RN3 rho f t * nA (f 3) (t 3)
def RD1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD0 rho * dA (f 0) (t 0)
def RD2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD1 rho f t * dA (f 1) (t 1)
def RD3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD2 rho f t * dA (f 2) (t 2)
def denR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RD3 rho f t * dA (f 3) (t 3)
def RS1 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS0 rho + sA (f 0) (t 0)
def RS2 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS1 rho f t + sA (f 1) (t 1)
def RS3 (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS2 rho f t + sA (f 2) (t 2)
def sgnR (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := RS3 rho f t + sA (f 3) (t 3)

theorem denR_pos (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : 0 < denR rho f t := by
  unfold denR RD3 RD2 RD1 RD0
  have := dA_pos (f 0) (t 0)
  have := dA_pos (f 1) (t 1)
  have := dA_pos (f 2) (t 2)
  have := dA_pos (f 3) (t 3)
  have := rho.den_pos
  positivity

/-- **The accumulators compute the coefficient**: `coefOfR = (-1)^σ · N / (D·K)`. -/
theorem coef_eqR (K : ℕ) (hK : 0 < K) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) :
    coefOfR K rho f t = (-1 : ℚ) ^ (sgnR rho f t) * (numR rho f t : ℚ) / ((denR rho f t * K : ℕ) : ℚ) := by
  have hK' : (K : ℚ) ≠ 0 := by exact_mod_cast hK.ne'
  have hr : (rho.den : ℚ) ≠ 0 := by exact_mod_cast rho.den_nz
  have h0 : (dA (f 0) (t 0) : ℚ) ≠ 0 := by exact_mod_cast (dA_pos (f 0) (t 0)).ne'
  have h1 : (dA (f 1) (t 1) : ℚ) ≠ 0 := by exact_mod_cast (dA_pos (f 1) (t 1)).ne'
  have h2 : (dA (f 2) (t 2) : ℚ) ≠ 0 := by exact_mod_cast (dA_pos (f 2) (t 2)).ne'
  have h3 : (dA (f 3) (t 3) : ℚ) ≠ 0 := by exact_mod_cast (dA_pos (f 3) (t 3)).ne'
  unfold coefOfR
  conv_lhs => rw [split_rat rho]
  rw [Fin.prod_univ_four, u_split, u_split, u_split, u_split]
  unfold sgnR RS3 RS2 RS1 RS0 numR RN3 RN2 RN1 RN0 denR RD3 RD2 RD1 RD0
  push_cast
  simp only [pow_add]
  field_simp

/-! ## The rho accumulator, docked -/

def accKept (j : Fin 30) : Prop := j.val < 4 ∨ j.val = 7

instance : DecidablePred accKept := fun j => by unfold accKept; infer_instance

theorem acc_step {U : Nat} (sl : Fin 30 → Fin U) (hsl : Function.Injective sl)
    (s : Bool) (n d c Qr S C Na Da sa : Nat) (hn : n < 2 ^ c) (hd : d < 2 ^ c) (A : Fin U → List Bool)
    (h0 : A (sl 0) = recW s n d c Qr) (h1 : A (sl 1) = ZeroPadding.pad S (List.replicate Na true))
    (h2 : A (sl 2) = ZeroPadding.pad S (List.replicate Da true))
    (h3 : A (sl 3) = ZeroPadding.pad S (List.replicate sa true))
    (h7 : A (sl 7) = List.replicate C false)
    (hscr : ∀ j : Fin 30, (j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ 8 ≤ j.val) → A (sl j) = List.replicate S false)
    (hf : AccFits c n d Na Da sa S C) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl accM) (accCost s n d c Na Da sa)
        (fun _ => 0) A (fun _ => 0) A' ∧
      A' (sl 4) = ZeroPadding.pad S (List.replicate (Na * n) true) ∧
      A' (sl 5) = ZeroPadding.pad S (List.replicate (Da * d) true) ∧
      A' (sl 6) = ZeroPadding.pad S (List.replicate (sa + s.toNat) true) ∧
      (∀ x, (∀ j, ¬ accKept j → sl j ≠ x) → A' x = A x) := by
  obtain ⟨L, hs, l4, l5, l6, lk, l7⟩ := acc_run s n d c Qr S S C Na Da sa hn hd (fun j => A (sl j)) h0 h1 h2 h3 h7
    hscr hf
  obtain ⟨st, sv, sk⟩ := dock_keep sl hsl A hs accKept (by
    intro j hj
    rcases hj with h | h
    · exact lk j h
    · have e : j = 7 := Fin.ext h
      subst e
      exact l7)
  exact ⟨_, st, (sv 4).trans l4, (sv 5).trans l5, (sv 6).trans l6, sk⟩

/-! ## The machine -/

def asl : Fin 30 → Fin 245 := ![8, 15, 16, 17, 18, 19, 20, 14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 40, 41, 42]
def tsl0 : Fin 32 → Fin 245 := ![0, 18, 19, 20, 43, 44, 45, 14, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
  60, 61, 62, 63, 64, 65, 66, 67, 4, 68]
def tsl1 : Fin 32 → Fin 245 := ![1, 43, 44, 45, 69, 70, 71, 14, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 87, 88, 89, 90, 91, 92, 93, 5, 94]
def tsl2 : Fin 32 → Fin 245 := ![2, 69, 70, 71, 95, 96, 97, 14, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
  110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 6, 120]
def tsl3 : Fin 32 → Fin 245 := ![3, 95, 96, 97, 121, 122, 123, 14, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
  135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 7, 146]
def usl1 : Fin 48 → Fin 245 := ![121, 122, 9, 14, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184,
  185, 186, 187, 188, 189, 190]
def usl2 : Fin 14 → Fin 245 := ![123, 187, 14, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]
def usl3 : Fin 49 → Fin 245 := ![10, 200, 201, 189, 14, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214,
  215, 216, 217, 218, 11, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 12, 233, 234, 235, 236, 237, 238,
  239, 240, 241, 242, 243, 244, 13]

/-- **The coefficient stage on the cursor's record multiplier**: one fixed machine (`Fin 245`). -/
def coefRM := Composition.machine (Count.oneM (15 : Fin 245) 14)
  (Composition.machine (Count.oneM (16 : Fin 245) 14)
  (Composition.machine (RecoveryFocus.machine asl accM)
  (Composition.machine (RecoveryFocus.machine tsl0 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl1 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl2 accSwM)
  (Composition.machine (RecoveryFocus.machine tsl3 accSwM)
  (Composition.machine (RecoveryFocus.machine usl1 divideM)
  (Composition.machine (RecoveryFocus.machine usl2 signM)
  (RecoveryFocus.machine usl3 emitM)))))))))

def gcdR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := Nat.gcd (numR rho f t) (denR rho f t * K)
def posR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  if sgnR rho f t % 2 = 0 then numR rho f t / gcdR K rho f t else 0
def negR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  if sgnR rho f t % 2 = 0 then 0 else numR rho f t / gcdR K rho f t
def dnR (K : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ := denR rho f t * K / gcdR K rho f t

def coefRCost (cw c0 K b : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) : ℕ :=
  (2 * 1 + 2) + 1 + ((2 * 1 + 2) + 1 +
  (accCost (decide (rho.num < 0)) rho.num.natAbs rho.den c0 1 1 0 + 1 +
  (accSwCost (f 0) (sS (f 0) (t 0)) (nS (f 0) (t 0)) (dS (f 0) (t 0)) cw (RN0 rho) (RD0 rho) (RS0 rho) + 1 +
  (accSwCost (f 1) (sS (f 1) (t 1)) (nS (f 1) (t 1)) (dS (f 1) (t 1)) cw (RN1 rho f t) (RD1 rho f t) (RS1 rho f t) + 1 +
  (accSwCost (f 2) (sS (f 2) (t 2)) (nS (f 2) (t 2)) (dS (f 2) (t 2)) cw (RN2 rho f t) (RD2 rho f t) (RS2 rho f t) + 1 +
  (accSwCost (f 3) (sS (f 3) (t 3)) (nS (f 3) (t 3)) (dS (f 3) (t 3)) cw (RN3 rho f t) (RD3 rho f t) (RS3 rho f t) + 1 +
  (divideCost (numR rho f t) (denR rho f t) K + 1 +
  (signCost (sgnR rho f t) (numR rho f t / gcdR K rho f t) + 1 +
  emitCost b (posR K rho f t) (negR K rho f t) (dnR K rho f t)))))))))

/-- Every blank-width premise of the stage, at exactly the values it runs on. -/
structure CoefFitsR (cw c0 K b : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) (S C : ℕ) : Prop where
  c1 : 1 ≤ C
  ar : AccFits c0 rho.num.natAbs rho.den 1 1 0 S C
  a0 : AccFits cw (nS (f 0) (t 0)) (dS (f 0) (t 0)) (RN0 rho) (RD0 rho) (RS0 rho) S C
  a1 : AccFits cw (nS (f 1) (t 1)) (dS (f 1) (t 1)) (RN1 rho f t) (RD1 rho f t) (RS1 rho f t) S C
  a2 : AccFits cw (nS (f 2) (t 2)) (dS (f 2) (t 2)) (RN2 rho f t) (RD2 rho f t) (RS2 rho f t) S C
  a3 : AccFits cw (nS (f 3) (t 3)) (dS (f 3) (t 3)) (RN3 rho f t) (RD3 rho f t) (RS3 rho f t) S C
  dv : DivideFits (numR rho f t) (denR rho f t) K S C
  sg : SignFits (sgnR rho f t) (numR rho f t / gcdR K rho f t) S C
  em : EmitFits b (posR K rho f t) (negR K rho f t) (dnR K rho f t) C

def recQ : Fin 4 → Fin 245 := ![0, 1, 2, 3]
def flagQ : Fin 4 → Fin 245 := ![4, 5, 6, 7]
def outQ : Fin 3 → Fin 245 := ![11, 12, 13]

theorem coefWordR_eq (b R K : ℕ) (hK : 0 < K) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) :
    coefWord b R (coefOfR K rho f t) 0 =
      ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) (posR K rho f t))) ∧
    coefWord b R (coefOfR K rho f t) 1 =
      ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) (negR K rho f t))) ∧
    coefWord b R (coefOfR K rho f t) 2 =
      ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) (dnR K rho f t))) := by
  have hD : 0 < denR rho f t * K := Nat.mul_pos (denR_pos rho f t) hK
  obtain ⟨hp, hn, hd⟩ := reduced (sgnR rho f t) (numR rho f t) (denR rho f t * K) hD
  rw [← coef_eqR K hK rho f t] at hp hn hd
  refine ⟨?_, ?_, ?_⟩
  · show ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b)
      (CompetitorMonomialProducts.positive (coefOfR K rho f t)))) = _
    rw [hp]
    rfl
  · show ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b)
      (CompetitorMonomialProducts.negative (coefOfR K rho f t)))) = _
    rw [hn]
    rfl
  · show ZeroPadding.pad R (frame (binary (CompetitorRationalDecision.width b) (coefOfR K rho f t).den)) = _
    rw [hd]
    rfl

/-! ## The run -/

theorem coefR_run (cw c0 K b Qr Qh Qf Qk Qb R S C : Nat) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ)
    (E : Fin 245 → List Bool)
    (hrec : ∀ i : Fin 4, f i = true →
      E (recQ i) = ZeroPadding.pad Qr (CloseoutRowsEstimatorCoefficients.Product.record cw (t i)))
    (hflag : ∀ i : Fin 4, E (flagQ i) = ZeroPadding.pad Qf [f i])
    (hrho : E 8 = ZeroPadding.pad Qh (CloseoutRowsEstimatorCoefficients.Product.record c0 rho))
    (hK : E 9 = ZeroPadding.pad Qk (List.replicate K true)) (hb : E 10 = ZeroPadding.pad Qb (List.replicate b true))
    (hout : ∀ i : Fin 3, E (outQ i) = List.replicate R false) (hlog : E 14 = List.replicate C false)
    (hscr : ∀ j : Fin 245, 15 ≤ j.val → E j = List.replicate S false)
    (hbits : ∀ i : Fin 4, f i = true → (t i).num.natAbs < 2 ^ cw ∧ (t i).den < 2 ^ cw)
    (hrb : rho.num.natAbs < 2 ^ c0 ∧ rho.den < 2 ^ c0)
    (hK0 : 0 < K) (hfit : CoefFitsR cw c0 K b rho f t S C) :
    ∃ E' : Fin 245 → List Bool, Step coefRM (coefRCost cw c0 K b rho f t) (fun _ => 0) E (fun _ => 0) E' ∧
      (∀ i : Fin 3, E' (outQ i) = coefWord b R (coefOfR K rho f t) i) ∧
      (∀ j : Fin 245, (j.val < 11 ∨ j.val = 14) → E' j = E j) := by
  have hz : ZeroPadding.pad S (List.replicate 0 true) = List.replicate S false := pad_nil S
  -- init: `1^1`, `1^1`
  have i1 := Count.one_step (15 : Fin 245) 14 (by decide) S C hfit.c1 (fun _ => 0) E rfl rfl
    (hscr 15 (by decide)) hlog
  set E1 := Function.update E (15 : Fin 245) (ZeroPadding.pad S (List.replicate 1 true)) with hE1
  have k1 : Keep 15 15 E E1 := keep_upd E 15 _
  have i2 := Count.one_step (16 : Fin 245) 14 (by decide) S C hfit.c1 (fun _ => 0) E1 rfl rfl
    ((k1 16 (by decide)).trans (hscr 16 (by decide))) ((k1 14 (by decide)).trans hlog)
  set E2 := Function.update E1 (16 : Fin 245) (ZeroPadding.pad S (List.replicate 1 true)) with hE2
  have k2 : Keep 16 16 E1 E2 := keep_upd E1 16 _
  have in2 : ∀ x : Fin 245, x.val < 15 → E2 x = E x := fun x hx =>
    (k2 x (Or.inl (by omega))).trans (k1 x (Or.inl (by omega)))
  have b2 : ∀ x : Fin 245, 16 < x.val → E2 x = List.replicate S false := fun x hx =>
    (k2 x (Or.inr hx)).trans ((k1 x (Or.inr (by omega))).trans (hscr x (by omega)))
  -- the multiplier record
  obtain ⟨F, sa, oa, ob, oc, ska⟩ := acc_step asl (by decide) (decide (rho.num < 0)) rho.num.natAbs rho.den c0 Qh S C
    1 1 0 hrb.1 hrb.2 E2 ((in2 8 (by decide)).trans (hrho.trans (record_eq c0 Qh rho)))
    ((k2 15 (by decide)).trans (by rw [hE1, Function.update_self])) (by show E2 16 = _; rw [hE2, Function.update_self])
    ((b2 17 (by decide)).trans hz.symm) ((in2 14 (by decide)).trans hlog)
    (fun j hj => b2 _ (by revert hj; fin_cases j <;> decide)) hfit.ar
  have kka : Keep 18 42 E2 F := keep_of asl E2 F accKept ska 18 42 (by decide)
  have in3 : ∀ x : Fin 245, x.val < 15 → F x = E x := fun x hx => (kka x (Or.inl (by omega))).trans (in2 x hx)
  have b3 : ∀ x : Fin 245, 42 < x.val → F x = List.replicate S false := fun x hx =>
    (kka x (Or.inr hx)).trans (b2 x (by omega))
  -- slot 0
  obtain ⟨hn0, hd0⟩ := slot_bits (f 0) (t 0) cw (hbits 0)
  obtain ⟨F0, st0, o0a, o0b, o0c, sk0⟩ := slot_step tsl0 (by decide) (f 0) (sS (f 0) (t 0)) (nS (f 0) (t 0))
    (dS (f 0) (t 0)) cw Qr Qf S C (RN0 rho) (RD0 rho) (RS0 rho) hn0 hd0 F
    (fun h => ((in3 0 (by decide)).trans (hrec 0 h)).trans (slot_record (f 0) (t 0) cw Qr h))
    oa ob oc ((in3 14 (by decide)).trans hlog) ((in3 4 (by decide)).trans (hflag 0))
    (fun j hj => b3 _ (by revert hj; fin_cases j <;> decide)) hfit.a0
  have kk0 : Keep 43 68 F F0 := keep_of tsl0 F F0 slotKept sk0 43 68 (by decide)
  rw [nS_mul] at o0a
  rw [dS_mul] at o0b
  rw [sS_add] at o0c
  -- slot 1
  obtain ⟨hn1, hd1⟩ := slot_bits (f 1) (t 1) cw (hbits 1)
  obtain ⟨F1, st1, o1a, o1b, o1c, sk1⟩ := slot_step tsl1 (by decide) (f 1) (sS (f 1) (t 1)) (nS (f 1) (t 1))
    (dS (f 1) (t 1)) cw Qr Qf S C (RN1 rho f t) (RD1 rho f t) (RS1 rho f t) hn1 hd1 F0
    (fun h => ((kk0 1 (by decide)).trans ((in3 1 (by decide)).trans (hrec 1 h))).trans
      (slot_record (f 1) (t 1) cw Qr h))
    o0a o0b o0c ((kk0 14 (by decide)).trans ((in3 14 (by decide)).trans hlog))
    ((kk0 5 (by decide)).trans ((in3 5 (by decide)).trans (hflag 1)))
    (fun j hj => (kk0 _ (by revert hj; fin_cases j <;> decide)).trans (b3 _ (by revert hj; fin_cases j <;> decide)))
    hfit.a1
  have kk1 : Keep 69 94 F0 F1 := keep_of tsl1 F0 F1 slotKept sk1 69 94 (by decide)
  rw [nS_mul] at o1a
  rw [dS_mul] at o1b
  rw [sS_add] at o1c
  -- slot 2
  obtain ⟨hn2, hd2⟩ := slot_bits (f 2) (t 2) cw (hbits 2)
  obtain ⟨F2, st2, o2a, o2b, o2c, sk2⟩ := slot_step tsl2 (by decide) (f 2) (sS (f 2) (t 2)) (nS (f 2) (t 2))
    (dS (f 2) (t 2)) cw Qr Qf S C (RN2 rho f t) (RD2 rho f t) (RS2 rho f t) hn2 hd2 F1
    (fun h => ((kk1 2 (by decide)).trans ((kk0 2 (by decide)).trans ((in3 2 (by decide)).trans (hrec 2 h)))).trans
      (slot_record (f 2) (t 2) cw Qr h))
    o1a o1b o1c ((kk1 14 (by decide)).trans ((kk0 14 (by decide)).trans ((in3 14 (by decide)).trans hlog)))
    ((kk1 6 (by decide)).trans ((kk0 6 (by decide)).trans ((in3 6 (by decide)).trans (hflag 2))))
    (fun j hj => (kk1 _ (by revert hj; fin_cases j <;> decide)).trans ((kk0 _ (by revert hj; fin_cases j <;> decide)).trans
      (b3 _ (by revert hj; fin_cases j <;> decide))))
    hfit.a2
  have kk2 : Keep 95 120 F1 F2 := keep_of tsl2 F1 F2 slotKept sk2 95 120 (by decide)
  rw [nS_mul] at o2a
  rw [dS_mul] at o2b
  rw [sS_add] at o2c
  -- slot 3
  obtain ⟨hn3, hd3⟩ := slot_bits (f 3) (t 3) cw (hbits 3)
  obtain ⟨F3, st3, o3a, o3b, o3c, sk3⟩ := slot_step tsl3 (by decide) (f 3) (sS (f 3) (t 3)) (nS (f 3) (t 3))
    (dS (f 3) (t 3)) cw Qr Qf S C (RN3 rho f t) (RD3 rho f t) (RS3 rho f t) hn3 hd3 F2
    (fun h => ((kk2 3 (by decide)).trans ((kk1 3 (by decide)).trans ((kk0 3 (by decide)).trans
      ((in3 3 (by decide)).trans (hrec 3 h))))).trans (slot_record (f 3) (t 3) cw Qr h))
    o2a o2b o2c
    ((kk2 14 (by decide)).trans ((kk1 14 (by decide)).trans ((kk0 14 (by decide)).trans ((in3 14 (by decide)).trans hlog))))
    ((kk2 7 (by decide)).trans ((kk1 7 (by decide)).trans ((kk0 7 (by decide)).trans ((in3 7 (by decide)).trans (hflag 3)))))
    (fun j hj => (kk2 _ (by revert hj; fin_cases j <;> decide)).trans ((kk1 _ (by revert hj; fin_cases j <;> decide)).trans
      ((kk0 _ (by revert hj; fin_cases j <;> decide)).trans (b3 _ (by revert hj; fin_cases j <;> decide)))))
    hfit.a3
  have kk3 : Keep 121 146 F2 F3 := keep_of tsl3 F2 F3 slotKept sk3 121 146 (by decide)
  rw [nS_mul] at o3a
  rw [dS_mul] at o3b
  rw [sS_add] at o3c
  have in7 : ∀ x : Fin 245, x.val < 15 → F3 x = E x := fun x hx =>
    (kk3 x (Or.inl (by omega))).trans ((kk2 x (Or.inl (by omega))).trans ((kk1 x (Or.inl (by omega))).trans
      ((kk0 x (Or.inl (by omega))).trans (in3 x hx))))
  have b7 : ∀ x : Fin 245, 146 < x.val → F3 x = List.replicate S false := fun x hx =>
    (kk3 x (Or.inr hx)).trans ((kk2 x (Or.inr (by omega))).trans ((kk1 x (Or.inr (by omega))).trans
      ((kk0 x (Or.inr (by omega))).trans (b3 x (by omega)))))
  -- the reduction: divide
  obtain ⟨L1, r1, r1o44, r1o46, r1k⟩ := divide_run (numR rho f t) (denR rho f t) K S Qk S C (fun j => F3 (usl1 j))
    o3a o3b ((in7 9 (by decide)).trans hK) ((in7 14 (by decide)).trans hlog)
    (fun j hj => b7 _ (by revert hj; fin_cases j <;> decide)) (denR_pos rho f t) hK0 hfit.dv
  obtain ⟨dr1, dv1, dk1⟩ := dock_keep usl1 (by decide) F3 r1 (fun j => j.val < 4) (fun j hj => r1k j hj)
  set G1 := install usl1 F3 L1 with hG1
  have kg1 : Keep 147 190 F3 G1 := keep_of usl1 F3 G1 (fun j => j.val < 4) dk1 147 190 (by decide)
  -- sign split
  obtain ⟨L2, r2, r2o12, r2o13, r2k⟩ := sign_run (sgnR rho f t) (numR rho f t / gcdR K rho f t) S S C
    (fun j => G1 (usl2 j)) ((kg1 123 (by decide)).trans o3c) ((dv1 44).trans r1o44)
    ((kg1 14 (by decide)).trans ((in7 14 (by decide)).trans hlog))
    (fun j hj => (kg1 _ (by revert hj; fin_cases j <;> decide)).trans (b7 _ (by revert hj; fin_cases j <;> decide)))
    hfit.sg
  obtain ⟨dr2, dv2, dk2⟩ := dock_keep usl2 (by decide) G1 r2 (fun j => j.val < 3) (fun j hj => r2k j hj)
  set G2 := install usl2 G1 L2 with hG2
  have kg2 : Keep 191 201 G1 G2 := keep_of usl2 G1 G2 (fun j => j.val < 3) dk2 191 201 (by decide)
  -- emit
  obtain ⟨L3, r3, r3o22, r3o35, r3o48, r3k⟩ := emit_run b (posR K rho f t) (negR K rho f t) (dnR K rho f t)
    Qb S R S C (fun j => G2 (usl3 j))
    ((kg2 10 (by decide)).trans ((kg1 10 (by decide)).trans ((in7 10 (by decide)).trans hb)))
    ((dv2 12).trans r2o12) ((dv2 13).trans r2o13) ((kg2 189 (by decide)).trans ((dv1 46).trans r1o46))
    ((kg2 14 (by decide)).trans ((kg1 14 (by decide)).trans ((in7 14 (by decide)).trans hlog)))
    (by
      intro j hj
      have hx : (usl3 j).val = 11 ∨ (usl3 j).val = 12 ∨ (usl3 j).val = 13 := by revert hj; fin_cases j <;> decide
      show G2 (usl3 j) = _
      rw [kg2 (usl3 j) (by omega), kg1 (usl3 j) (by omega), in7 (usl3 j) (by omega)]
      rcases hx with h | h | h
      · have e : usl3 j = outQ 0 := Fin.ext h
        rw [e]
        exact hout 0
      · have e : usl3 j = outQ 1 := Fin.ext h
        rw [e]
        exact hout 1
      · have e : usl3 j = outQ 2 := Fin.ext h
        rw [e]
        exact hout 2)
    (fun j h5 h22 h35 h48 => (kg2 _ (by revert h5 h22 h35 h48; fin_cases j <;> decide)).trans
      ((kg1 _ (by revert h5 h22 h35 h48; fin_cases j <;> decide)).trans
      (b7 _ (by revert h5 h22 h35 h48; fin_cases j <;> decide))))
    hfit.em
  obtain ⟨dr3, dv3, dk3⟩ := dock_keep usl3 (by decide) G2 r3 (fun j => j.val < 5) (fun j hj => r3k j hj)
  have hall : Step coefRM _ (fun _ => 0) E (fun _ => 0) (install usl3 G2 L3) :=
    i1.seq (i2.seq (sa.seq (st0.seq (st1.seq (st2.seq (st3.seq (dr1.seq (dr2.seq dr3))))))))
  obtain ⟨w0, w1, w2⟩ := coefWordR_eq b R K hK0 rho f t
  refine ⟨_, hall, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ((dv3 22).trans r3o22).trans w0.symm
    · exact ((dv3 35).trans r3o35).trans w1.symm
    · exact ((dv3 48).trans r3o48).trans w2.symm
  · intro j hj
    rw [dk3 j (by intro k hk e; subst e; revert hk hj; fin_cases k <;> decide)]
    rw [kg2 j (Or.inl (by omega)), kg1 j (Or.inl (by omega)), in7 j (by omega)]

theorem coefR_step {U : Nat} (sl : Fin 245 → Fin U) (hsl : Function.Injective sl)
    (cw c0 K b Qr Qh Qf Qk Qb R S C : Nat) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hrec : ∀ i : Fin 4, f i = true →
      A (sl (recQ i)) = ZeroPadding.pad Qr (CloseoutRowsEstimatorCoefficients.Product.record cw (t i)))
    (hflag : ∀ i : Fin 4, A (sl (flagQ i)) = ZeroPadding.pad Qf [f i])
    (hrho : A (sl 8) = ZeroPadding.pad Qh (CloseoutRowsEstimatorCoefficients.Product.record c0 rho))
    (hK : A (sl 9) = ZeroPadding.pad Qk (List.replicate K true))
    (hb : A (sl 10) = ZeroPadding.pad Qb (List.replicate b true))
    (hout : ∀ i : Fin 3, A (sl (outQ i)) = List.replicate R false) (hlog : A (sl 14) = List.replicate C false)
    (hscr : ∀ j : Fin 245, 15 ≤ j.val → A (sl j) = List.replicate S false)
    (hbits : ∀ i : Fin 4, f i = true → (t i).num.natAbs < 2 ^ cw ∧ (t i).den < 2 ^ cw)
    (hrb : rho.num.natAbs < 2 ^ c0 ∧ rho.den < 2 ^ c0)
    (hK0 : 0 < K) (hfit : CoefFitsR cw c0 K b rho f t S C) :
    ∃ A' : Fin U → List Bool, Step (RecoveryFocus.machine sl coefRM) (coefRCost cw c0 K b rho f t) H A H A' ∧
      (∀ i : Fin 3, A' (sl (outQ i)) = coefWord b R (coefOfR K rho f t) i) ∧
      (∀ x, (∀ j : Fin 245, sl j = x → (j.val < 11 ∨ j.val = 14)) → A' x = A x) := by
  obtain ⟨E', hs, ho, hk⟩ := coefR_run cw c0 K b Qr Qh Qf Qk Qb R S C rho f t (fun j => A (sl j)) hrec hflag hrho
    hK hb hout hlog hscr hbits hrb hK0 hfit
  refine ⟨_, dz hs sl hsl H A hH (fun _ => rfl), fun i => (install_slot sl hsl A E' _).trans (ho i), ?_⟩
  intro x hx
  by_cases hex : ∃ j, sl j = x
  · obtain ⟨j, rfl⟩ := hex
    rw [install_slot sl hsl]
    exact hk j (hx j rfl)
  · exact install_other sl A E' x (fun j e => hex ⟨j, e⟩)

/-- One source-polynomial size: `V` bounds every numerator magnitude and denominator read (the multiplier's and the
term coefficients'), `w` the record widths. -/
def coefBigR (V K b w : ℕ) : ℕ := 32 * V ^ 5 * (K + 1) + 8 * b + 8 * w + 128

theorem coefFitsR_of_big (cw c0 K b V : ℕ) (rho : ℚ) (f : Fin 4 → Bool) (t : Fin 4 → ℚ) (S C : ℕ)
    (hV : 1 ≤ V) (hnV : ∀ i : Fin 4, f i = true → (t i).num.natAbs < V ∧ (t i).den < V)
    (hrV : rho.num.natAbs < V ∧ rho.den < V) (hbits : ∀ i : Fin 4, f i = true → (t i).num.natAbs < 2 ^ cw ∧ (t i).den < 2 ^ cw)
    (hS : coefBigR V K b (cw + c0) ≤ S) (hC : coefBigR V K b (cw + c0) ≤ C) : CoefFitsR cw c0 K b rho f t S C := by
  have hsplit : coefBigR V K b (cw + c0) = 32 * (V ^ 4 * V) + 32 * ((V ^ 4 * V) * K) + 8 * b + 8 * (cw + c0) + 128 := by
    unfold coefBigR
    ring
  rw [hsplit] at hS hC
  set X := V ^ 4 with hX
  have hXT : X ≤ X * V := Nat.le_mul_of_pos_right X hV
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ hV
  have hKZ : K ≤ (X * V) * K := Nat.le_mul_of_pos_left K (by nlinarith)
  have a0 := nA_le (f 0) (t 0) V hV (fun h => (hnV 0 h).1)
  have a1 := nA_le (f 1) (t 1) V hV (fun h => (hnV 1 h).1)
  have a2 := nA_le (f 2) (t 2) V hV (fun h => (hnV 2 h).1)
  have a3 := nA_le (f 3) (t 3) V hV (fun h => (hnV 3 h).1)
  have e0 := dA_le (f 0) (t 0) V hV (fun h => (hnV 0 h).2)
  have e1 := dA_le (f 1) (t 1) V hV (fun h => (hnV 1 h).2)
  have e2 := dA_le (f 2) (t 2) V hV (fun h => (hnV 2 h).2)
  have e3 := dA_le (f 3) (t 3) V hV (fun h => (hnV 3 h).2)
  have s0 := sA_le (f 0) (t 0)
  have s1 := sA_le (f 1) (t 1)
  have s2 := sA_le (f 2) (t 2)
  have s3 := sA_le (f 3) (t 3)
  have hsr : (decide (rho.num < 0)).toNat ≤ 1 := Bool.toNat_le _
  have nv : ∀ i : Fin 4, nS (f i) (t i) < V ∧ dS (f i) (t i) < V := by
    intro i
    unfold nS dS
    cases h : f i
    · refine ⟨?_, ?_⟩ <;> simp <;> omega
    · simpa using hnV i h
  have p2 : V ≤ V ^ 2 := Nat.le_self_pow (by decide) V
  have p23 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have p34 : V ^ 3 ≤ X := Nat.pow_le_pow_right (by omega) (by decide)
  have hN0 : RN0 rho ≤ V := by unfold RN0; omega
  have hN1 : RN1 rho f t ≤ V ^ 2 := by
    unfold RN1
    rw [pow_two]
    exact Nat.mul_le_mul hN0 a0
  have hN2 : RN2 rho f t ≤ V ^ 3 := by
    unfold RN2
    rw [pow_succ]
    exact Nat.mul_le_mul hN1 a1
  have hN3 : RN3 rho f t ≤ X := by
    unfold RN3
    rw [hX, pow_succ]
    exact Nat.mul_le_mul hN2 a2
  have hN4 : numR rho f t ≤ X * V := by
    unfold numR
    exact Nat.mul_le_mul hN3 a3
  have hD0 : RD0 rho ≤ V := by unfold RD0; omega
  have hD1 : RD1 rho f t ≤ V ^ 2 := by
    unfold RD1
    rw [pow_two]
    exact Nat.mul_le_mul hD0 e0
  have hD2 : RD2 rho f t ≤ V ^ 3 := by
    unfold RD2
    rw [pow_succ]
    exact Nat.mul_le_mul hD1 e1
  have hD3 : RD3 rho f t ≤ X := by
    unfold RD3
    rw [hX, pow_succ]
    exact Nat.mul_le_mul hD2 e2
  have hD4 : denR rho f t ≤ X * V := by
    unfold denR
    exact Nat.mul_le_mul hD3 e3
  have hDK : denR rho f t * K ≤ (X * V) * K := Nat.mul_le_mul_right K hD4
  have hDKm : denR rho f t * (2 * K + 3) ≤ 2 * ((X * V) * K) + 3 * (X * V) := by
    calc denR rho f t * (2 * K + 3) ≤ (X * V) * (2 * K + 3) := Nat.mul_le_mul_right _ hD4
      _ = 2 * ((X * V) * K) + 3 * (X * V) := by ring
  have hS0 : RS0 rho ≤ 5 := by unfold RS0; omega
  have hS1 : RS1 rho f t ≤ 5 := by unfold RS1 RS0; omega
  have hS2 : RS2 rho f t ≤ 5 := by unfold RS2 RS1 RS0; omega
  have hS3 : RS3 rho f t ≤ 5 := by unfold RS3 RS2 RS1 RS0; omega
  have hsg : sgnR rho f t ≤ 5 := by unfold sgnR RS3 RS2 RS1 RS0; omega
  have hq : numR rho f t / gcdR K rho f t ≤ numR rho f t := Nat.div_le_self _ _
  have hdq : dnR K rho f t ≤ denR rho f t * K := Nat.div_le_self _ _
  have hpq : posR K rho f t ≤ numR rho f t := by unfold posR; split <;> omega
  have hnq : negR K rho f t ≤ numR rho f t := by unfold negR; split <;> omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact accFits_of _ _ _ _ _ _ S C X V hV hrV.1 hrV.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · exact accFits_of _ _ _ _ _ _ S C X V hV (nv 0).1 (nv 0).2 (by omega) (by omega) hS0 (by omega) (by omega)
      (by omega)
  · exact accFits_of _ _ _ _ _ _ S C X V hV (nv 1).1 (nv 1).2 (by omega) (by omega) hS1 (by omega) (by omega)
      (by omega)
  · exact accFits_of _ _ _ _ _ _ S C X V hV (nv 2).1 (nv 2).2 (by omega) (by omega) hS2 (by omega) (by omega)
      (by omega)
  · exact accFits_of _ _ _ _ _ _ S C X V hV (nv 3).1 (nv 3).2 (by omega) (by omega) hS3 (by omega) (by omega)
      (by omega)
  · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega⟩

end
end NearCubicWires.SourceFactorSel.CoefR

