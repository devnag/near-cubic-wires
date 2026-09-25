import Proof.Rows.RowsInitThrInitWords
import Proof.Rows.RowsInitThrLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace RowsInit.ThrInitRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction RowsConstruction.BaseLayout PCJd4d1d9d7d1fa4313_Production
open RowsInit.VecDock RowsInit.ThrInitWords
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj inst_out rw_eq)
noncomputable section

section Fan
variable {k m : ℕ} (select : Fin m → Option (Fin k)) (data : Fin k → List Bool) (D : ℕ)

theorem fin_in (v : ℕ) (hv : v < k + (m + 1) + 1) :
    ExtIncidence.NativeFanout.input data D ⟨v, hv⟩ =
      if h : v < k then data ⟨v, h⟩ else if v = k + m then List.replicate D true else [] := by
  by_cases h1 : v < k + (m + 1)
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.castAdd 1 (⟨v, h1⟩ : Fin (k + (m + 1))) := rfl
    rw [e]; unfold ExtIncidence.NativeFanout.input; rw [Fin.addCases_left]
    by_cases h2 : v < k
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.castAdd (m + 1) (⟨v, h2⟩ : Fin k) := rfl
      rw [e2, Fin.addCases_left, dif_pos h2]
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.natAdd k (⟨v - k, by omega⟩ : Fin (m + 1)) :=
        Fin.ext (by simp; omega)
      rw [e2, Fin.addCases_right, dif_neg h2]
      by_cases h3 : v - k < m
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.castAdd 1 (⟨v - k, h3⟩ : Fin m) := rfl
        rw [e3, Fin.addCases_left, if_neg (by omega)]
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp; omega)
        rw [e3, Fin.addCases_right, if_pos (by omega)]
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.natAdd (k + (m + 1)) (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [e]; unfold ExtIncidence.NativeFanout.input; rw [Fin.addCases_right, dif_neg (by omega), if_neg (by omega)]

theorem fin_out (v : ℕ) (hv : v < k + (m + 1) + 1) :
    ExtIncidence.NativeFanout.output select data D ⟨v, hv⟩ =
      if h : v < k then data ⟨v, h⟩ else if h2 : v < k + m then
        ZeroPadding.pad D ((select ⟨v - k, by omega⟩).elim [] data)
      else if v = k + m then List.replicate D true else List.replicate (D + 1) false := by
  by_cases h1 : v < k + (m + 1)
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.castAdd 1 (⟨v, h1⟩ : Fin (k + (m + 1))) := rfl
    rw [e]; unfold ExtIncidence.NativeFanout.output; rw [Fin.addCases_left]
    by_cases h2 : v < k
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.castAdd (m + 1) (⟨v, h2⟩ : Fin k) := rfl
      rw [e2, Fin.addCases_left, dif_pos h2]
    · have e2 : (⟨v, h1⟩ : Fin (k + (m + 1))) = Fin.natAdd k (⟨v - k, by omega⟩ : Fin (m + 1)) :=
        Fin.ext (by simp; omega)
      rw [e2, Fin.addCases_right, dif_neg h2]
      by_cases h3 : v - k < m
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.castAdd 1 (⟨v - k, h3⟩ : Fin m) := rfl
        rw [e3, Fin.addCases_left, dif_pos (by omega)]
        simp only [ExtIncidence.NativeFanout.word]
      · have e3 : (⟨v - k, by omega⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) := Fin.ext (by simp; omega)
        rw [e3, Fin.addCases_right, dif_neg (by omega), if_pos (by omega)]
  · have e : (⟨v, hv⟩ : Fin (k + (m + 1) + 1)) = Fin.natAdd (k + (m + 1)) (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [e]; unfold ExtIncidence.NativeFanout.output
    rw [Fin.addCases_right, dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]

theorem fan_dock {u : ℕ} (sl : Fin (k + (m + 1) + 1) → Fin u) (hi : Function.Injective sl)
    (hD : ∀ i, (data i).length ≤ D) (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0)
    (hs : ∀ (v : ℕ) (hv : v < k), A (sl ⟨v, by omega⟩) = data ⟨v, hv⟩)
    (hd : A (sl ⟨k + m, by omega⟩) = List.replicate D true)
    (hb : ∀ (v : ℕ) (hv : v < k + (m + 1) + 1), k ≤ v → v ≠ k + m → A (sl ⟨v, hv⟩) = []) :
    Step (RecoveryFocus.machine sl (ExtIncidence.NativeFanout.machine select)) (2 * D + 4) H A H
      (install sl A (ExtIncidence.NativeFanout.output select data D)) := by
  refine run_dock (Step.of_ready (ExtIncidence.NativeFanout.ready select data D hD)) sl hi H A hH (fun l => ?_)
  obtain ⟨v, hv⟩ := l
  rw [fin_in]
  by_cases h1 : v < k
  · rw [dif_pos h1]; exact hs v h1
  · rw [dif_neg h1]
    by_cases h2 : v = k + m
    · subst h2; rw [if_pos rfl]; exact hd
    · rw [if_neg h2]; exact hb v hv (by omega) h2

end Fan

/-! ## 2. The fixed `init` indices and the three slot maps -/

/-- The `init` index of word `j` of `thrInitWord` (`oT` = the scratch region). -/
def wDst (oT : ℕ) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 40 | 3 => 41 | 4 => 42 | 5 => 43 | 6 => 46 | 7 => 47 | 8 => 48 | 9 => 50
  | 10 => 52 | 11 => 115 | 12 => 116 | 13 => 127 | 14 => 128 | 15 => 129 | 16 => 130 | 17 => 131
  | 18 => 132 | 19 => 133 | 20 => 134 | 21 => 135 | 22 => 39 | 23 => 98 | 24 => oT | 25 => oT + 1
  | 26 => oT + 2 | 27 => oT + 3 | 28 => oT + 4 | 29 => oT + 5 | 30 => 145 | _ => 145

/-- The `init` index of the `U`-fanout's destination `d`. -/
def uDst (d : ℕ) : ℕ :=
  if d < 2 then 44 + d else if d = 2 then 49 else if d < 47 then 51 + d else if d < 62 then 53 + d
  else if d < 66 then 59 + d else if d = 66 then 53 else if d = 67 then 126 else 125

/-- The `U`-fanout's selection: blanks, `word 0..3`, `fb wT 1` twice, `tape N`. -/
def selU (d : Fin 69) : Option (Fin 6) :=
  if d.val < 62 then none else if h : d.val < 66 then some ⟨d.val - 62, by omega⟩
  else if d.val < 68 then some 4 else some 5

def selR (_ : Fin 36) : Option (Fin 0) := none

/-! Left inverses (injectivity by `congrArg`). -/

def wInv0 : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 40 => 2 | 41 => 3 | 42 => 4 | 43 => 5 | 46 => 6 | 47 => 7 | 48 => 8 | 50 => 9
  | 52 => 10 | 115 => 11 | 116 => 12 | 127 => 13 | 128 => 14 | 129 => 15 | 130 => 16 | 131 => 17
  | 132 => 18 | 133 => 19 | 134 => 20 | 135 => 21 | 39 => 22 | 98 => 23 | _ => 30

def wInv (oT x : ℕ) : ℕ := if oT ≤ x then 24 + (x - oT) else wInv0 x

def uInv (x : ℕ) : ℕ :=
  if x ≤ 45 then x - 44 else if x = 49 then 2 else if 54 ≤ x ∧ x ≤ 97 then x - 51
  else if 100 ≤ x ∧ x ≤ 114 then x - 53 else if 121 ≤ x ∧ x ≤ 124 then x - 59 else if x = 53 then 66
  else if x = 126 then 67 else 68

theorem wDst_lt (oT j : ℕ) (hj : j < 31) :
    (wDst oT j < 146 ∧ wDst oT j ≠ 0 ∨ j = 0 ∧ wDst oT j = 0) ∨ (oT ≤ wDst oT j ∧ wDst oT j < oT + 6) := by
  interval_cases j <;> simp only [wDst, true_and, and_true, or_true, true_or] <;> omega

theorem wInv_wDst (oT j : ℕ) (hT : 146 ≤ oT) (hj : j < 31) : wInv oT (wDst oT j) = j := by
  interval_cases j <;> simp only [wDst] <;> unfold wInv <;>
    first | (rw [if_pos (by omega)]; omega) | (rw [if_neg (by omega)]; rfl)

theorem uDst_lt (d : ℕ) (hd : d < 69) : 44 ≤ uDst d ∧ uDst d ≤ 126 ∧ uDst d ≠ 98 ∧ uDst d ≠ 99 := by
  unfold uDst; split_ifs <;> omega

theorem uInv_uDst (d : ℕ) (hd : d < 69) : uInv (uDst d) = d := by
  unfold uDst; split_ifs <;> unfold uInv <;> split_ifs <;> omega

section Maps
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (cD dD cU dU : ℕ)

/-- The scratch the stage needs past `oT`: six fanout sources and the vector stage's scratch (+1 for the mask). -/
def need : ℕ := 7 + (initVec a bnd bndW cD dD cU dU).extra

def f1 (oT v : ℕ) : ℕ := if v = 0 then 0 else if v ≤ 31 then 2 + wDst oT (v - 1) else 2 + oT + 6 + (v - 32)
def fR (v : ℕ) : ℕ := if v < 36 then 2 + (v + 2) else if v = 36 then 2 + 39 else 2 + 38
def fU (oT v : ℕ) : ℕ := if v < 6 then 2 + oT + v else if v < 75 then 2 + uDst (v - 6) else if v = 75 then 2 + 98
  else 2 + 99

def g1 (oT x : ℕ) : ℕ := if x = 0 then 0 else if 2 + oT + 6 ≤ x then 32 + (x - (2 + oT + 6)) else 1 + wInv oT (x - 2)
def gR (x : ℕ) : ℕ := if x = 41 then 36 else if x = 40 then 37 else x - 4
def gU (oT x : ℕ) : ℕ :=
  if 2 + oT ≤ x ∧ x < 2 + oT + 6 then x - (2 + oT) else if x = 100 then 75 else if x = 101 then 76 else 6 + uInv (x - 2)

theorem g1_f1 (oT v : ℕ) (hT : 146 ≤ oT) : g1 oT (f1 oT v) = v := by
  unfold f1 g1
  by_cases v0 : v = 0
  · rw [if_pos v0, if_pos rfl, v0]
  rw [if_neg v0]
  by_cases v1 : v ≤ 31
  · rw [if_pos v1]
    have hl := wDst_lt oT (v - 1) (by omega)
    have hi := wInv_wDst oT (v - 1) hT (by omega)
    rw [if_neg (by omega), if_neg (by omega), show 2 + wDst oT (v - 1) - 2 = wDst oT (v - 1) by omega, hi]
    omega
  · rw [if_neg v1, if_neg (by omega), if_pos (by omega)]
    omega

theorem gR_fR (v : ℕ) (hv : v < 38) : gR (fR v) = v := by
  unfold fR gR; split_ifs <;> omega

theorem gU_fU (oT v : ℕ) (hT : 146 ≤ oT) (hv : v < 77) : gU oT (fU oT v) = v := by
  unfold fU gU
  by_cases v1 : v < 6
  · rw [if_pos v1, if_pos (by omega)]; omega
  rw [if_neg v1]
  by_cases v2 : v < 75
  · rw [if_pos v2]
    have hl := uDst_lt (v - 6) (by omega)
    have hi := uInv_uDst (v - 6) (by omega)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show 2 + uDst (v - 6) - 2 = uDst (v - 6) by omega, hi]
    omega
  · rw [if_neg v2]
    by_cases v3 : v = 75
    · rw [if_pos v3, if_neg (by omega), if_pos rfl]; omega
    · rw [if_neg v3, if_neg (by omega), if_neg (by omega), if_pos rfl]; omega

def sl1 (NI oT : ℕ) := vmap NI (1 + 31 + (initVec a bnd bndW cD dD cU dU).extra + 1) (f1 oT)
def slR (NI : ℕ) := vmap NI (0 + (36 + 1) + 1) fR
def slU (NI oT : ℕ) := vmap NI (6 + (69 + 1) + 1) (fU oT)

variable (NI oT : ℕ) (hT : 146 ≤ oT) (hNI : oT + need a bnd bndW cD dD cU dU ≤ NI)

include hNI in
theorem b1 : ∀ v, v < 1 + 31 + (initVec a bnd bndW cD dD cU dU).extra + 1 → f1 oT v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f1
  by_cases v0 : v = 0
  · rw [if_pos v0]; omega
  rw [if_neg v0]
  by_cases v1 : v ≤ 31
  · rw [if_pos v1]; have := wDst_lt oT (v - 1) (by omega); omega
  · rw [if_neg v1]; omega

theorem bR : ∀ v, v < 0 + (36 + 1) + 1 → fR v < 2 + rowsWork NI := by
  intro v hv; rw [rw_eq]; unfold fR; split_ifs <;> omega

include hNI in
theorem bU : ∀ v, v < 6 + (69 + 1) + 1 → fU oT v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold fU
  by_cases v1 : v < 6
  · rw [if_pos v1]; omega
  rw [if_neg v1]
  by_cases v2 : v < 75
  · rw [if_pos v2]; have := uDst_lt (v - 6) (by omega); omega
  · rw [if_neg v2]; split_ifs <;> omega

include hT hNI in
theorem inj1 : Function.Injective (sl1 a bnd bndW cD dD cU dU NI oT) :=
  vmap_inj (b1 a bnd bndW cD dD cU dU NI oT hNI) (by
    intro v w _ _ h
    have := congrArg (g1 oT) h
    rwa [g1_f1 oT v hT, g1_f1 oT w hT] at this)

theorem injR : Function.Injective (slR NI) := vmap_inj (bR NI) (by
  intro v w hv hw h
  have := congrArg gR h
  rwa [gR_fR v hv, gR_fR w hw] at this)

include hT hNI in
theorem injU : Function.Injective (slU NI oT) := vmap_inj (bU a bnd bndW cD dD cU dU NI oT hNI) (by
  intro v w hv hw h
  have := congrArg (gU oT) h
  rwa [gU_fU oT v hT hv, gU_fU oT w hT hw] at this)

end Maps

/-! ## 3. Disjointness tables -/

theorem wDst_R (oT j : ℕ) (hT : 146 ≤ oT) (hj : j < 31) : wDst oT j ≤ 1 ∨ 39 ≤ wDst oT j := by
  interval_cases j <;> simp only [wDst] <;> omega

theorem wDst_ne99 (oT j : ℕ) (hT : 146 ≤ oT) (hj : j < 31) : wDst oT j ≠ 99 := by
  interval_cases j <;> simp only [wDst] <;> omega

theorem uDst_cases (d : ℕ) (hd : d < 69) :
    uDst d = 44 ∨ uDst d = 45 ∨ uDst d = 49 ∨ uDst d = 53 ∨ (54 ≤ uDst d ∧ uDst d ≤ 97) ∨
      (100 ≤ uDst d ∧ uDst d ≤ 114) ∨ (121 ≤ uDst d ∧ uDst d ≤ 126) := by
  unfold uDst; split_ifs <;> omega

theorem w_ne_u (oT j d : ℕ) (hT : 146 ≤ oT) (hj : j < 31) (hd : d < 69) : wDst oT j ≠ uDst d := by
  intro h
  have hu := uDst_cases d hd
  interval_cases j <;> simp only [wDst] at h <;> omega

theorem wDst_22 (oT : ℕ) : wDst oT 22 = 39 := rfl
theorem wDst_src (oT v : ℕ) (hv : v < 6) : wDst oT (24 + v) = oT + v := by
  interval_cases v <;> rfl

/-! ## 4. Docked banks by value -/

theorem inst_at {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (hi : Function.Injective (vmap NI n f)) (A : Fin (2 + rowsWork NI) → List Bool) (B : Fin n → List Bool)
    (x : Fin (2 + rowsWork NI)) (v : ℕ) (hv : v < n) (hx : x.val = f v) :
    install (vmap NI n f) A B x = B ⟨v, hv⟩ := by
  rw [show x = vmap NI n f ⟨v, hv⟩ from Fin.ext (hx.trans (vmap_val hb ⟨v, hv⟩).symm)]
  exact install_slot _ hi _ _ _

theorem inst_off {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (A : Fin (2 + rowsWork NI) → List Bool) (B : Fin n → List Bool) (x : Fin (2 + rowsWork NI))
    (h : ∀ v, v < n → f v ≠ x.val) : install (vmap NI n f) A B x = A x :=
  install_other _ _ _ _ (fun j hj => h j.val j.isLt (by rw [← hj, vmap_val hb]))

/-! ## 5. The machine, its cost, the fanout data -/

section Machine
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (cD dD cU dU : ℕ) (NI oT : ℕ)

def m1 := RecoveryFocus.machine (sl1 a bnd bndW cD dD cU dU NI oT)
  (MaskedReset.machine (initVec a bnd bndW cD dD cU dU).machine (fun _ => true))
def mR := RecoveryFocus.machine (slR NI) (ExtIncidence.NativeFanout.machine selR)
def mU := RecoveryFocus.machine (slU NI oT) (ExtIncidence.NativeFanout.machine selU)

/-- **The THR `init`-word writer** (one fixed machine per `a`, the cascade-bound stages, the constants, `NI`, `oT`). -/
def machine := Composition.machine (Composition.machine (m1 a bnd bndW cD dD cU dU NI oT) (mR NI)) (mU NI oT)

/-- The `U`-fanout's six sources. -/
def dataU (r : Request) : Fin 6 → List Bool := fun i => thrInitWord a bnd cD dD cU dU ⟨24 + i.val, by omega⟩ r

/-- Its cost at a request. -/
def cost (r : Request) : ℕ :=
  ((2 * (initVec a bnd bndW cD dD cU dU).cost r + 2) + 1 + (2 * rpVal a r + 4)) + 1 +
    (2 * ThrBaseBounds.UOf' cD dD cU dU (r.input a).length + 4)

end Machine

theorem dataU_len (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (cD dD cU dU : ℕ) (r : Request)
    (hU : 4 * (12 * (r.input a).length + 19) + 3 ≤ ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
    (hc : RowsInit.LoopFan.circOf r ≤ 4) (i : Fin 6) :
    (dataU a bnd cD dD cU dU r i).length ≤ ThrBaseBounds.UOf' cD dD cU dU (r.input a).length := by
  fin_cases i <;> simp [dataU, thrInitWord, RepairSource.VerifierDecoding.CompareMachine.word,
    UnaryTemplate.tape] <;> omega

theorem circOf_le (r : Request) : RowsInit.LoopFan.circOf r ≤ 4 := by
  cases r with
  | terminal => exact Nat.zero_le _
  | sym r four _ _ => exact four
  | thr r four _ _ => exact four

theorem pad_nil (K : ℕ) : ZeroPadding.pad K [] = List.replicate K false := by
  simp [ZeroPadding.pad]

theorem wDst_98 (oT j : ℕ) (hT : 146 ≤ oT) (hj : j < 31) (h : wDst oT j = 98) : j = 23 := by
  interval_cases j <;> simp only [wDst] at h ⊢ <;> omega

theorem wDst_39 (oT j : ℕ) (hT : 146 ≤ oT) (hj : j < 31) (h : wDst oT j = 39) : j = 22 := by
  interval_cases j <;> simp only [wDst] at h ⊢ <;> omega

theorem wDst_hi (oT j : ℕ) (hj : j < 31) (h : oT ≤ wDst oT j) (hT : 146 ≤ oT) : 24 ≤ j ∧ j ≤ 29 := by
  interval_cases j <;> simp only [wDst] at h ⊢ <;> omega

/-! ## 6. The three stages -/

section Stages
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (cD dD cU dU : ℕ) (NI oT : ℕ) (hT : 146 ≤ oT) (hNI : oT + need a bnd bndW cD dD cU dU ≤ NI)
include hT hNI

theorem st1 (r : Request) (A : Fin (2 + rowsWork NI) → List Bool) (h0 : A (pubPort NI 0) = frame (r.input a))
    (hF : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A x = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oT ≤ x.val → x.val < 2 + oT + need a bnd bndW cD dD cU dU → A x = []) :
    ∃ B : Fin (1 + 31 + (initVec a bnd bndW cD dD cU dU).extra + 1) → List Bool,
      Step (m1 a bnd bndW cD dD cU dU NI oT) (2 * (initVec a bnd bndW cD dD cU dU).cost r + 2) (fun _ => 0) A
        (fun _ => 0) (install (sl1 a bnd bndW cD dD cU dU NI oT) A B) ∧
      B ⟨0, by omega⟩ = frame (r.input a) ∧
      ∀ j : Fin 31, B ⟨j.val + 1, by omega⟩ = thrInitWord a bnd cD dD cU dU j r := by
  have hb := b1 a bnd bndW cD dD cU dU NI oT hNI
  obtain ⟨B, hs, b0, bj⟩ := vec_dock (initVec a bnd bndW cD dD cU dU) r (sl1 a bnd bndW cD dD cU dU NI oT)
    (inj1 a bnd bndW cD dD cU dU NI oT hT hNI) (fun _ => 0) A (fun _ => rfl)
    (by
      rw [show sl1 a bnd bndW cD dD cU dU NI oT ⟨0, by omega⟩ = pubPort NI 0 from
        Fin.ext (by rw [sl1, vmap_val hb]; rfl), h0])
    (by
      intro j hj
      have hv : (sl1 a bnd bndW cD dD cU dU NI oT j).val = f1 oT j.val := vmap_val hb j
      have hl := j.isLt
      unfold f1 at hv
      rw [if_neg hj] at hv
      unfold need at hS
      by_cases h31 : j.val ≤ 31
      · rw [if_pos h31] at hv
        rcases wDst_lt oT (j.val - 1) (by omega) with hw | hw
        · exact hF _ (by omega) (by omega)
        · exact hS _ (by omega) (by omega)
      · rw [if_neg h31] at hv
        exact hS _ (by omega) (by omega))
  refine ⟨B, hs, b0, fun j => ?_⟩
  fin_cases j <;> exact bj _ (by omega)

omit hT hNI in
theorem stR (Rp : ℕ) (A1 : Fin (2 + rowsWork NI) → List Bool) (hd : A1 (wp NI 41) = List.replicate Rp true)
    (hb : ∀ x : Fin (2 + rowsWork NI), 4 ≤ x.val → x.val ≤ 40 → A1 x = []) :
    Step (mR NI) (2 * Rp + 4) (fun _ => 0) A1 (fun _ => 0)
      (install (slR NI) A1 (ExtIncidence.NativeFanout.output selR (fun i : Fin 0 => i.elim0) Rp)) := by
  have hbR := bR NI
  refine fan_dock selR (fun i : Fin 0 => i.elim0) Rp (slR NI) (injR NI)
    (fun i => i.elim0) (fun _ => 0) A1 (fun _ => rfl) (fun v hv => absurd hv (Nat.not_lt_zero _)) ?_ ?_
  · have hw : 41 < 2 + rowsWork NI := by rw [rw_eq]; omega
    rw [show slR NI ⟨0 + 36, by omega⟩ = wp NI 41 from Fin.ext (by rw [slR, vmap_val hbR, wp_val hw]; rfl)]
    exact hd
  · intro v hv _ h2
    have hx : (slR NI ⟨v, hv⟩).val = fR v := vmap_val hbR ⟨v, hv⟩
    unfold fR at hx
    exact hb _ (by split_ifs at hx <;> omega) (by split_ifs at hx <;> omega)

theorem stU (r : Request) (A2 : Fin (2 + rowsWork NI) → List Bool)
    (hU : 4 * (12 * (r.input a).length + 19) + 3 ≤ ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
    (hs : ∀ (v : ℕ) (hv : v < 6), A2 (wp NI (2 + oT + v)) = dataU a bnd cD dD cU dU r ⟨v, hv⟩)
    (hd : A2 (wp NI 100) = List.replicate (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length) true)
    (hbd : ∀ d, d < 69 → A2 (wp NI (2 + uDst d)) = []) (hl : A2 (wp NI 101) = []) :
    Step (mU NI oT) (2 * ThrBaseBounds.UOf' cD dD cU dU (r.input a).length + 4) (fun _ => 0) A2 (fun _ => 0)
      (install (slU NI oT) A2 (ExtIncidence.NativeFanout.output selU (dataU a bnd cD dD cU dU r)
        (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length))) := by
  have hbU := bU a bnd bndW cD dD cU dU NI oT hNI
  refine fan_dock selU (dataU a bnd cD dD cU dU r) _ (slU NI oT) (injU a bnd bndW cD dD cU dU NI oT hT hNI)
    (dataU_len a bnd cD dD cU dU r hU (circOf_le r)) (fun _ => 0) A2 (fun _ => rfl) ?_ ?_ ?_
  · intro v hv
    have hw : 2 + oT + v < 2 + rowsWork NI := by
      have := hbU v (by omega); unfold fU at this; rw [if_pos hv] at this; exact this
    rw [show slU NI oT ⟨v, by omega⟩ = wp NI (2 + oT + v) from Fin.ext (by
      rw [slU, vmap_val hbU, wp_val hw]; simp only [fU, if_pos hv])]
    exact hs v hv
  · have hw : 100 < 2 + rowsWork NI := by rw [rw_eq]; omega
    rw [show slU NI oT ⟨6 + 69, by omega⟩ = wp NI 100 from Fin.ext (by rw [slU, vmap_val hbU, wp_val hw]; rfl)]
    exact hd
  · intro v hv h1 h2
    by_cases h3 : v < 75
    · have hw : 2 + uDst (v - 6) < 2 + rowsWork NI := by
        have := uDst_lt (v - 6) (by omega); rw [rw_eq]; omega
      rw [show slU NI oT ⟨v, hv⟩ = wp NI (2 + uDst (v - 6)) from Fin.ext (by
        rw [slU, vmap_val hbU, wp_val hw]; simp only [fU, if_neg (show ¬ v < 6 by omega), if_pos h3])]
      exact hbd _ (by omega)
    · have hw : 101 < 2 + rowsWork NI := by rw [rw_eq]; omega
      rw [show slU NI oT ⟨v, hv⟩ = wp NI 101 from Fin.ext (by
        rw [slU, vmap_val hbU, wp_val hw]; simp only [fU, if_neg (show ¬ v < 6 by omega), if_neg h3,
          if_neg (show ¬ v = 75 by omega)])]
      exact hl

end Stages

/-! ## 7. The run -/

section Run
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (cD dD cU dU : ℕ) (NI oT : ℕ) (hT : 146 ≤ oT) (hNI : oT + need a bnd bndW cD dD cU dU ≤ NI)
include hT hNI

theorem words_run (r : Request) (A : Fin (2 + rowsWork NI) → List Bool)
    (hU : 4 * (12 * (r.input a).length + 19) + 3 ≤ ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
    (h0 : A (pubPort NI 0) = frame (r.input a))
    (hF : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A x = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oT ≤ x.val → x.val < 2 + oT + need a bnd bndW cD dD cU dU → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a bnd bndW cD dD cU dU NI oT) (cost a bnd bndW cD dD cU dU r) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ j : Fin 31, A' (wp NI (2 + wDst oT j.val)) = thrInitWord a bnd cD dD cU dU j r) ∧
      (∀ v, v < 36 → A' (wp NI (4 + v)) = List.replicate (rpVal a r) false) ∧
      A' (wp NI 40) = List.replicate (rpVal a r + 1) false ∧
      (∀ d : Fin 69, A' (wp NI (2 + uDst d.val)) = ZeroPadding.pad (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
        ((selU d).elim [] (dataU a bnd cD dD cU dU r))) ∧
      A' (wp NI 101) = List.replicate (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length + 1) false ∧
      A' (wp NI 53) = A (wp NI 53) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 ≤ x.val ∧ x.val < 148) →
        ¬ (2 + oT ≤ x.val ∧ x.val < 2 + oT + need a bnd bndW cD dD cU dU) → A' x = A x) := by
  have hn := hNI
  unfold need at hn
  have hneed : 7 ≤ need a bnd bndW cD dD cU dU := by unfold need; omega
  have h1b := b1 a bnd bndW cD dD cU dU NI oT hNI
  have hRb := bR NI
  have hUb := bU a bnd bndW cD dD cU dU NI oT hNI
  have i1 := inj1 a bnd bndW cD dD cU dU NI oT hT hNI
  have iR := injR NI
  have iU := injU a bnd bndW cD dD cU dU NI oT hT hNI
  set U := ThrBaseBounds.UOf' cD dD cU dU (r.input a).length with hUdef
  obtain ⟨B, s1, b0, bj⟩ := st1 a bnd bndW cD dD cU dU NI oT hT hNI r A h0 hF hS
  set A1 := install (sl1 a bnd bndW cD dD cU dU NI oT) A B with hA1
  -- `A1` off `sl1`: untouched
  have a1_off : ∀ x : Fin (2 + rowsWork NI), x.val ≠ 0 → (∀ j, j < 31 → x.val ≠ 2 + wDst oT j) →
      ¬ (2 + oT + 6 ≤ x.val ∧ x.val < 2 + oT + need a bnd bndW cD dD cU dU) → A1 x = A x := by
    intro x hx0 hxw hxs
    refine inst_off h1b A B x (fun v hv h => ?_)
    unfold f1 at h
    unfold need at hxs
    by_cases v0 : v = 0
    · rw [if_pos v0] at h; exact hx0 h.symm
    rw [if_neg v0] at h
    by_cases v1 : v ≤ 31
    · rw [if_pos v1] at h; exact hxw (v - 1) (by omega) h.symm
    · rw [if_neg v1] at h; exact hxs ⟨by omega, by omega⟩
  have a1_w : ∀ (j : ℕ) (hj : j < 31), A1 (wp NI (2 + wDst oT j)) = thrInitWord a bnd cD dD cU dU ⟨j, hj⟩ r := by
    intro j hj
    have hw := wDst_lt oT j hj
    have hv : 2 + wDst oT j < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hf : (wp NI (2 + wDst oT j)).val = f1 oT (j + 1) := by
      rw [wp_val hv]
      unfold f1
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]
    rw [hA1, sl1, inst_at h1b i1 A B _ (j + 1) (by omega) hf]
    exact bj ⟨j, hj⟩
  -- stage R
  have sR := stR NI (rpVal a r) A1 (by
      have := a1_w 22 (by omega); rw [wDst_22] at this; exact this) (by
      intro x hx1 hx2
      rw [a1_off x (by omega) (fun j hj h => by have := wDst_R oT j hT hj; omega) (by unfold need; omega)]
      exact hF x (by omega) (by omega))
  set A2 := install (slR NI) A1 (ExtIncidence.NativeFanout.output selR (fun i : Fin 0 => i.elim0) (rpVal a r))
    with hA2
  have a2_off : ∀ x : Fin (2 + rowsWork NI), ¬ (4 ≤ x.val ∧ x.val ≤ 41) → A2 x = A1 x := by
    intro x hx
    refine inst_off hRb A1 _ x (fun v hv h => hx ?_)
    unfold fR at h; split_ifs at h <;> omega
  -- stage U
  have sU := stU a bnd bndW cD dD cU dU NI oT hT hNI r A2 hU (by
      intro v hv
      have hj : 24 + v < 31 := by omega
      have e : 2 + oT + v = 2 + wDst oT (24 + v) := by rw [wDst_src oT v hv]; omega
      rw [a2_off _ (by rw [wp_val (by rw [rw_eq]; omega)]; omega), e, a1_w (24 + v) hj]
      rfl) (by
      rw [a2_off _ (by rw [wp_val (by rw [rw_eq]; omega)]; omega), show (100 : ℕ) = 2 + wDst oT 23 from rfl,
        a1_w 23 (by omega)]
      rfl) (by
      intro d hd
      have hu := uDst_lt d hd
      have hv : 2 + uDst d < 2 + rowsWork NI := by rw [rw_eq]; omega
      rw [a2_off _ (by rw [wp_val hv]; omega), a1_off _ (by rw [wp_val hv]; omega)
        (fun j hj h => by rw [wp_val hv] at h; exact w_ne_u oT j d hT hj hd (by omega))
        (by rw [wp_val hv]; unfold need; omega)]
      exact hF _ (by rw [wp_val hv]; omega) (by rw [wp_val hv]; omega)) (by
      have hv : 101 < 2 + rowsWork NI := by rw [rw_eq]; omega
      rw [a2_off _ (by rw [wp_val hv]; omega), a1_off _ (by rw [wp_val hv]; omega)
        (fun j hj h => by rw [wp_val hv] at h; exact wDst_ne99 oT j hT hj (by omega))
        (by rw [wp_val hv]; unfold need; omega)]
      exact hF _ (by rw [wp_val hv]; omega) (by rw [wp_val hv]; omega))
  set A3 := install (slU NI oT) A2 (ExtIncidence.NativeFanout.output selU (dataU a bnd cD dD cU dU r) U) with hA3
  have a3_off : ∀ x : Fin (2 + rowsWork NI), ¬ (2 + oT ≤ x.val ∧ x.val < 2 + oT + 6) →
      (∀ d, d < 69 → x.val ≠ 2 + uDst d) → x.val ≠ 100 → x.val ≠ 101 → A3 x = A2 x := by
    intro x hxs hxd h100 h101
    refine inst_off hUb A2 _ x (fun v hv h => ?_)
    unfold fU at h
    by_cases v1 : v < 6
    · rw [if_pos v1] at h; exact hxs ⟨by omega, by omega⟩
    rw [if_neg v1] at h
    by_cases v2 : v < 75
    · rw [if_pos v2] at h; exact hxd (v - 6) (by omega) h.symm
    rw [if_neg v2] at h
    split_ifs at h <;> omega
  refine ⟨A3, ((s1.seq sR).seq sU).congr rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the 31 words
    rintro ⟨jv, hj⟩
    have hw := wDst_lt oT jv hj
    have hv : 2 + wDst oT jv < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hpv : (wp NI (2 + wDst oT jv)).val = 2 + wDst oT jv := wp_val hv
    by_cases hs : 24 ≤ jv ∧ jv ≤ 29
    · have e := wDst_src oT (jv - 24) (by omega)
      rw [show 24 + (jv - 24) = jv by omega] at e
      have hf : (wp NI (2 + wDst oT jv)).val = fU oT (jv - 24) := by
        rw [hpv, e]; unfold fU; rw [if_pos (by omega)]; omega
      rw [hA3, slU, inst_at hUb iU A2 _ _ (jv - 24) (by omega) hf, fin_out, dif_pos (by omega)]
      simp only [dataU]
      congr 2
      first | omega | (apply Fin.ext; simp only; omega)
    have hlo : wDst oT jv < 146 := by
      rcases hw with hw | hw
      · omega
      · have := wDst_hi oT jv hj hw.1 hT; omega
    by_cases h23 : jv = 23
    · subst h23
      have hf : (wp NI (2 + wDst oT 23)).val = fU oT 75 := by rw [hpv]; rfl
      rw [hA3, slU, inst_at hUb iU A2 _ _ 75 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega), if_pos rfl]
      rfl
    have n98 : wDst oT jv ≠ 98 := fun h => h23 (wDst_98 oT jv hT hj h)
    have n99 := wDst_ne99 oT jv hT hj
    have hU3 : A3 (wp NI (2 + wDst oT jv)) = A2 (wp NI (2 + wDst oT jv)) := by
      refine a3_off _ (by rw [hpv]; omega) (fun d hd h => ?_) (by rw [hpv]; omega) (by rw [hpv]; omega)
      rw [hpv] at h
      exact w_ne_u oT jv d hT hj hd (by omega)
    rw [hU3]
    by_cases h22 : jv = 22
    · subst h22
      have hf : (wp NI (2 + wDst oT 22)).val = fR 36 := by rw [hpv]; rfl
      rw [hA2, slR, inst_at hRb iR A1 _ _ 36 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega), if_pos rfl]
      rfl
    have n39 : wDst oT jv ≠ 39 := fun h => h22 (wDst_39 oT jv hT hj h)
    have hR3 := wDst_R oT jv hT hj
    have hU2 : A2 (wp NI (2 + wDst oT jv)) = A1 (wp NI (2 + wDst oT jv)) :=
      a2_off _ (by rw [hpv]; omega)
    rw [hU2]
    exact a1_w jv hj
  · intro v hv
    have hw : 4 + v < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hpv : (wp NI (4 + v)).val = 4 + v := wp_val hw
    have hU3 : A3 (wp NI (4 + v)) = A2 (wp NI (4 + v)) := by
      refine a3_off _ (by rw [hpv]; omega) (fun d hd h => ?_) (by rw [hpv]; omega) (by rw [hpv]; omega)
      have := uDst_lt d hd
      rw [hpv] at h
      omega
    have hf : (wp NI (4 + v)).val = fR v := by rw [hpv]; unfold fR; rw [if_pos hv]; omega
    rw [hU3, hA2, slR, inst_at hRb iR A1 _ _ v (by omega) hf, fin_out, dif_neg (by omega), dif_pos (by omega)]
    simp only [selR, Option.elim, pad_nil]
  · have hw : 40 < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hpv : (wp NI 40).val = 40 := wp_val hw
    have hU3 : A3 (wp NI 40) = A2 (wp NI 40) := by
      refine a3_off _ (by rw [hpv]; omega) (fun d hd h => ?_) (by rw [hpv]; omega) (by rw [hpv]; omega)
      have := uDst_lt d hd
      rw [hpv] at h
      omega
    have hf : (wp NI 40).val = fR 37 := by rw [hpv]; rfl
    rw [hU3, hA2, slR, inst_at hRb iR A1 _ _ 37 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega),
      if_neg (by omega)]
  · intro d
    have hu := uDst_lt d.val d.isLt
    have hw : 2 + uDst d.val < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hf : (wp NI (2 + uDst d.val)).val = fU oT (6 + d.val) := by
      rw [wp_val hw]; unfold fU; rw [if_neg (by omega), if_pos (by omega)]; congr 2; omega
    rw [hA3, slU, inst_at hUb iU A2 _ _ (6 + d.val) (by omega) hf, fin_out, dif_neg (by omega), dif_pos (by omega)]
    congr 3
    first | omega | (apply Fin.ext; simp only; omega)
  · have hw : 101 < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hf : (wp NI 101).val = fU oT 76 := by rw [wp_val hw]; rfl
    rw [hA3, slU, inst_at hUb iU A2 _ _ 76 (by omega) hf, fin_out, dif_neg (by omega), dif_neg (by omega),
      if_neg (by omega)]
  · have hw : 53 < 2 + rowsWork NI := by rw [rw_eq]; omega
    have hpv : (wp NI 53).val = 53 := wp_val hw
    have hU3 : A3 (wp NI 53) = A2 (wp NI 53) := by
      refine a3_off _ (by rw [hpv]; omega) (fun d hd h => ?_) (by rw [hpv]; omega) (by rw [hpv]; omega)
      have := uDst_cases d hd
      rw [hpv] at h
      omega
    rw [hU3, a2_off _ (by rw [hpv]; omega)]
    refine a1_off _ (by rw [hpv]; omega) (fun j hj h => ?_) (by rw [hpv]; omega)
    rw [hpv] at h
    interval_cases j <;> simp only [wDst] at h <;> omega
  · intro x hx1 hx2
    have hU3 : A3 x = A2 x := by
      refine a3_off _ (by omega) (fun d hd h => ?_) (by omega) (by omega)
      have := uDst_lt d hd
      omega
    have hU2 : A2 x = A1 x := a2_off _ (by omega)
    rw [hU3, hU2]
    by_cases hx0 : x.val = 0
    · have ex : x = pubPort NI 0 := Fin.ext hx0
      have hf : x.val = f1 oT 0 := by rw [hx0]; rfl
      rw [hA1, sl1, inst_at h1b i1 A B _ 0 (by omega) hf, b0, ex, h0]
    · refine a1_off _ hx0 (fun j hj h => ?_) (by omega)
      have := wDst_lt oT j hj
      omega

end Run

end
end RowsInit.ThrInitRun
