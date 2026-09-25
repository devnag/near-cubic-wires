import Proof.Packets.SourceParamsK

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget.Pow2
open NearCubicWires.SourceBudget NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
open NearCubicWires.SourceBudget.Params
noncomputable section

/-! ## 1. Rounding up to a power of two -/

/-- `m·2^x` rounded up to a power of two, with a unary-computable exponent. -/
def up (m x : ℕ) : ℕ := 2^(Nat.clog 2 (m+1) + x)

theorem pow_clog_ge (m : ℕ) : m + 1 ≤ 2^(Nat.clog 2 (m+1)) := Nat.le_pow_clog (by norm_num) (m+1)

theorem pow_clog_le (m : ℕ) : 2^(Nat.clog 2 (m+1)) ≤ 2*m + 2 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have h1 : 1 < m + 1 := by omega
    have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < Nat.clog 2 (m+1) := Nat.clog_pos (by norm_num) h1
    have e2 : (Nat.clog 2 (m+1)).pred + 1 = Nat.clog 2 (m+1) := Nat.succ_pred_eq_of_pos hpos
    have e : 2^(Nat.clog 2 (m+1)) = 2^((Nat.clog 2 (m+1)).pred) * 2 := by
      rw [← pow_succ, e2]
    omega

theorem le_up (m x : ℕ) : m * 2^x ≤ up m x := by
  unfold up
  rw [pow_add]
  exact Nat.mul_le_mul_right _ (by have := pow_clog_ge m; omega)

theorem up_le (m x : ℕ) : up m x ≤ (2*m + 2) * 2^x := by
  unfold up
  rw [pow_add]
  exact Nat.mul_le_mul_right _ (pow_clog_le m)

/-- A class bound `c·(q+1)^h·2^x` rounded: `up (c·(q+1)^h) x ≤ (2c+2)·(q+1)^h·2^x`. -/
theorem up_class (c h q x : ℕ) : up (c*(q+1)^h) x ≤ (2*c+2)*((q+1)^h*2^x) := by
  have h1 : 1 ≤ (q+1)^h := Nat.one_le_pow _ _ (by omega)
  have hu := up_le (c*(q+1)^h) x
  have e : (2*c+2)*((q+1)^h*2^x) = (2*(c*(q+1)^h) + 2*(q+1)^h)*2^x := by ring
  rw [e]
  exact hu.trans (Nat.mul_le_mul_right _ (by omega))

/-! ## 2. The rounded caps, each `2^y` with `y` in closed form (`C` stays exact: see the header) -/

section params
variable (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)

/-- The exponent of `hF'`. -/
def yH (L q : ℕ) : ℕ :=
  Nat.clog 2 (hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L*
    (q+1)^hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L + 1) + q/4
/-- The exponent of `cC'`'s table part. -/
def yA (L q : ℕ) : ℕ :=
  Nat.clog 2 (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + (q - normalizedLiveCount q L)
/-- The exponent of `cC'`'s small part. -/
def yB (q : ℕ) : ℕ :=
  Nat.clog 2 (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + q/4
/-- The exponent of `Vv'`. -/
def yV (L q : ℕ) : ℕ :=
  Nat.clog 2 (v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + (q - normalizedLiveCount q L)
/-- The exponent of `rR'`. -/
def yR (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) : ℕ :=
  Nat.clog 2 (((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1)*
    (q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p) + 1) + q/4

/-- **`capsU`'s header fuel, rounded**. -/
def hFOf2 (L q : ℕ) : ℕ := 2^(yH selector s p L q)
/-- **`capsU`'s copy cap, rounded** (one power of two above the table part plus the small part). -/
def cCOf2 (L q : ℕ) : ℕ := 2^(max (yA selector s p L q) (yB selector s p q) + 1)
/-- **`V = capsU`'s descriptor reserve, rounded**. -/
def VvOf2 (L q : ℕ) : ℕ := 2^(yV selector s p L q)
/-- **`capsU`'s raw reserve, rounded**. -/
def rROf2 (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) : ℕ := 2^(yR selector s p packets q)

/-! ### Lower bounds (the old values) -/

theorem hFOf_le (L q : ℕ) : hFOf selector s p L q ≤ hFOf2 selector s p L q := by
  have h := le_up (hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L*
    (q+1)^hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L) (q/4)
  unfold hFOf smallClass
  rw [← mul_assoc]
  exact h

theorem VvOf1_le (L q : ℕ) :
    v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
      tableClass L (v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q ≤ VvOf2 selector s p L q := by
  have h := le_up (v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) (q - normalizedLiveCount q L)
  unfold tableClass
  rw [← mul_assoc]
  exact h

theorem cCOf1_le (L q : ℕ) :
    cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
        tableClass L (cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q +
      cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
        smallClass 4 (cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q ≤ cCOf2 selector s p L q := by
  have hA := le_up (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) (q - normalizedLiveCount q L)
  have hB := le_up (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    (q+1)^cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) (q/4)
  have mA : 2^(yA selector s p L q) ≤ 2^(max (yA selector s p L q) (yB selector s p q)) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have mB : 2^(yB selector s p q) ≤ 2^(max (yA selector s p L q) (yB selector s p q)) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have e : 2^(max (yA selector s p L q) (yB selector s p q) + 1) = 2*2^(max (yA selector s p L q) (yB selector s p q)) := by
    rw [pow_succ]; ring
  unfold cCOf2 tableClass smallClass
  rw [e, ← mul_assoc, ← mul_assoc]
  unfold up at hA hB
  change _ ≤ 2^(yA selector s p L q) at hA
  change _ ≤ 2^(yB selector s p q) at hB
  omega

theorem rROf_le (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) :
    rROf selector packets s p q ≤ rROf2 selector s p packets q := by
  have h := le_up (((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1)*
    (q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p)) (q/4)
  unfold rROf smallClass
  rw [← mul_assoc]
  exact h

/-! ### Upper bounds (the classes, at most `2×` / `4×`) -/

theorem hFOf2_le (L q : ℕ) : hFOf2 selector s p L q ≤
    (2*hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L + 2)*
      smallClass 4 (hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L) q :=
  up_class _ _ q (q/4)

theorem cCOf2_le (L q : ℕ) : cCOf2 selector s p L q ≤
    (4*cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 4)*
        tableClass L (cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q +
      (4*cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 4)*
        smallClass 4 (cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q := by
  have hA := up_class (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p))
    (cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q (q - normalizedLiveCount q L)
  have hB := up_class (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p))
    (cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q (q/4)
  have hmax : 2^(max (yA selector s p L q) (yB selector s p q)) ≤ 2^(yA selector s p L q) + 2^(yB selector s p q) := by
    rcases le_total (yA selector s p L q) (yB selector s p q) with h | h
    · rw [max_eq_right h]; exact Nat.le_add_left _ _
    · rw [max_eq_left h]; exact Nat.le_add_right _ _
  have e : 2^(max (yA selector s p L q) (yB selector s p q) + 1) = 2*2^(max (yA selector s p L q) (yB selector s p q)) := by
    rw [pow_succ]; ring
  unfold cCOf2 tableClass smallClass
  unfold up at hA hB
  change 2^(yA selector s p L q) ≤ _ at hA
  change 2^(yB selector s p q) ≤ _ at hB
  rw [e]
  have e2 : ∀ c X : ℕ, (4*c+4)*X = 2*((2*c+2)*X) := fun c X => by ring
  rw [e2, e2]
  omega

theorem rROf2_le (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (q : ℕ) : rROf2 selector s p packets q ≤
    (2*((packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1) + 2)*
      smallClass 4 (rowsE (decompositionOf s) p.clauseDegree (tgt s p)) q :=
  up_class _ _ q (q/4)

/-! ## 4. The caps fit at the rounded values -/

theorem capsFit2 (den : ℕ) (hden : 1 ≤ den) (r : Request) (hr : RequestAdmitted den p.clauseDegree (tgt s p) r)
    (layout : Packets.Layout (decompositionOf s) (r.family (decompositionOf s)) (geometryOf selector (decompositionOf s) r))
    (hdw : layout.degree ≤ r.q) (hC : layout.C = COf selector s p r.q)
    (hK : normalizedLiveCount r.q r.liveScale + r.q/4 ≤ r.q) :
    RCFive.NativeResources.streamCap (decompositionOf s) (r.family (decompositionOf s))
        (geometryOf selector (decompositionOf s) r) layout ≤ layout.C ∧
      (RCFive.RowCaps.chosen selector (decompositionOf s) (printerOf s) r layout).headerFuel ≤
        hFOf2 selector s p r.liveScale r.q ∧
      (RCFive.RowCaps.chosen selector (decompositionOf s) (printerOf s) r layout).copyCap ≤
        cCOf2 selector s p r.liveScale r.q ∧
      (RCFive.RowCaps.chosen selector (decompositionOf s) (printerOf s) r layout).descriptorReserve ≤
        VvOf2 selector s p r.liveScale r.q ∧
      RCFive.NativeResources.driverCap (decompositionOf s) (r.family (decompositionOf s))
        (geometryOf selector (decompositionOf s) r) layout (printerOf s) ≤ VvOf2 selector s p r.liveScale r.q := by
  have hlC : layout.C ≤ cc0 selector (decompositionOf s) p.clauseDegree (tgt s p)*
      smallClass 4 (ce0 selector (decompositionOf s) p.clauseDegree (tgt s p)) r.q := le_of_eq hC
  have hv := v0_spec selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) den hden r hr layout hdw hlC hK
  have hV := VvOf1_le selector s p r.liveScale r.q
  refine ⟨?_, ?_, ?_, hv.2.trans hV, hv.1.trans hV⟩
  · rw [hC]
    exact cc0_spec selector (decompositionOf s) p.clauseDegree (tgt s p) den hden r hr layout hdw
  · exact (hd0_spec selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) r.liveScale den hden r hr rfl layout hdw).trans
      (hFOf_le selector s p r.liveScale r.q)
  · exact (cp0_spec selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) den hden r hr layout hdw hlC).trans
      (cCOf1_le selector s p r.liveScale r.q)

/-- **`rawFit` at the rounded raw reserve.** -/
theorem rawFit2 (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (r : Request) (raw : ℕ)
    (hraw : raw ≤ packetBudget (decompositionOf s) (packets (decompositionOf s)).coefficient
      (packets (decompositionOf s)).degree r + 1)
    (hrows : (r.family (decompositionOf s)).rows.length + 1 ≤
      rowsC (decompositionOf s) p.clauseDegree (tgt s p)*(r.q+1)^rowsE (decompositionOf s) p.clauseDegree (tgt s p))
    (hsm : (r.smallSize (decompositionOf s))^(packets (decompositionOf s)).degree ≤ 1*smallClass 4 0 r.q) :
    raw ≤ rROf2 selector s p packets r.q :=
  (rawFit selector packets s p r raw hraw hrows hsm).trans (rROf_le selector s p packets r.q)

end params

/-! ## 5. `KF` at the rounded classes -/

end
end NearCubicWires.SourceBudget.Pow2

