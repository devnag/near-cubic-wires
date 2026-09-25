import Proof.Rows.RowsInitThrInitRun
import Proof.Rows.RowsPrimeReserve
import Proof.Rows.RowsKeyZeroMode

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace RowsInit.ThrInitReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.SupplierPipeline
open RowsConstruction RowsConstruction.BaseLayout PCJd4d1d9d7d1fa4313_Production
open RowsInit.ThrInitWords RowsInit.ThrInitRun
open RowsInit.ThrLoop (wp wp_val rw_eq)
noncomputable section

/-! ## 1. The fixed index maps -/

section Idx
variable (NI : ℕ) (h : 146 ≤ NI)
def ini : Fin 40 → Fin NI := fun m => ⟨m.val, by omega⟩
def ix : Fin 4 → Fin NI := fun c => ⟨40 + c.val, by omega⟩
def ib : Fin 82 → Fin NI := fun k => ⟨44 + k.val, by omega⟩
def iOne : Fin NI := ⟨126, by omega⟩
def iz : Fin 9 → Fin NI := fun m => ⟨127 + m.val, by omega⟩
def iniS : Fin 9 → Fin NI := fun m => ⟨136 + m.val, by omega⟩
def iMode : Fin NI := ⟨145, by omega⟩

theorem ini_inj : Function.Injective (ini NI h) := fun x y e => Fin.ext (by simpa [ini] using congrArg Fin.val e)
theorem ib_inj : Function.Injective (ib NI h) := fun x y e => Fin.ext (by
  have := congrArg Fin.val e; simp [ib] at this; omega)
theorem iz_inj : Function.Injective (iz NI h) := fun x y e => Fin.ext (by
  have := congrArg Fin.val e; simp [iz] at this; omega)
theorem ib9_ne : ib NI h 9 ≠ iOne NI h := by
  intro e; have := congrArg Fin.val e; simp [ib, iOne] at this

/-- An `init` port by value. -/
theorem pw (i : Fin NI) (v : ℕ) (hv : 2 + i.val = v) : initPort NI i = wp NI v := by
  have hl := i.isLt
  apply Fin.ext
  rw [RowsInit.ThrLoop.init_val, wp_val (by rw [rw_eq]; omega)]
  exact hv
end Idx

/-- **The value clauses of `ThrInitRun.words_run`** on the fixed area (words `j < 24` and `30`, the two fanouts, port 53). -/
def WordsAt (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (cD dD cU dU NI oT : ℕ) (r : Request)
    (A : Fin (2 + rowsWork NI) → List Bool) : Prop :=
  (∀ j : Fin 31, (j.val < 24 ∨ j.val = 30) → A (wp NI (2 + wDst oT j.val)) = thrInitWord a bnd cD dD cU dU j r) ∧
  (∀ v, v < 36 → A (wp NI (4 + v)) = List.replicate (rpVal a r) false) ∧
  A (wp NI 40) = List.replicate (rpVal a r + 1) false ∧
  (∀ d : Fin 69, A (wp NI (2 + uDst d.val)) = ZeroPadding.pad (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
    ((selU d).elim [] (dataU a bnd cD dD cU dU r))) ∧
  A (wp NI 101) = List.replicate (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length + 1) false ∧
  A (wp NI 53) = []

/-- `WordsAt` only reads ports in `[2, 148)`. -/
theorem wordsAt_transport (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (cD dD cU dU NI oT : ℕ)
    (hT : 146 ≤ oT) (r : Request) (A B : Fin (2 + rowsWork NI) → List Bool)
    (hA : WordsAt a bnd cD dD cU dU NI oT r A)
    (hAB : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → B x = A x) :
    WordsAt a bnd cD dD cU dU NI oT r B := by
  have hw : ∀ v, 2 ≤ v → v < 148 → B (wp NI v) = A (wp NI v) := fun v h1 h2 =>
    hAB _ (by rw [wp_val (by rw [rw_eq]; omega)]; exact h1) (by rw [wp_val (by rw [rw_eq]; omega)]; exact h2)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  refine ⟨fun j hj => ?_, fun v hv => ?_, ?_, fun d => ?_, ?_, ?_⟩
  · have := wDst_lt oT j.val j.isLt
    have hlo : wDst oT j.val < 146 := by
      rcases this with h | h
      · omega
      · have := wDst_hi oT j.val j.isLt h.1 hT; omega
    rw [hw _ (by omega) (by omega)]; exact h1 j hj
  · rw [hw _ (by omega) (by omega)]; exact h2 v hv
  · rw [hw _ (by omega) (by omega)]; exact h3
  · have := uDst_lt d.val d.isLt
    rw [hw _ (by omega) (by omega)]; exact h4 d
  · rw [hw _ (by omega) (by omega)]; exact h5
  · rw [hw _ (by omega) (by omega)]; exact h6

/-- `words_run`'s exit satisfies `WordsAt`. -/
theorem wordsAt_of_run (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (cD dD cU dU NI oT : ℕ) (r : Request)
    (A A' : Fin (2 + rowsWork NI) → List Bool) (hA53 : A (wp NI 53) = [])
    (h1 : ∀ j : Fin 31, A' (wp NI (2 + wDst oT j.val)) = thrInitWord a bnd cD dD cU dU j r)
    (h2 : ∀ v, v < 36 → A' (wp NI (4 + v)) = List.replicate (rpVal a r) false)
    (h3 : A' (wp NI 40) = List.replicate (rpVal a r + 1) false)
    (h4 : ∀ d : Fin 69, A' (wp NI (2 + uDst d.val)) = ZeroPadding.pad (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length)
      ((selU d).elim [] (dataU a bnd cD dD cU dU r)))
    (h5 : A' (wp NI 101) = List.replicate (ThrBaseBounds.UOf' cD dD cU dU (r.input a).length + 1) false)
    (h6 : A' (wp NI 53) = A (wp NI 53)) :
    WordsAt a bnd cD dD cU dU NI oT r A' :=
  ⟨fun j _ => h1 j, h2, h3, h4, h5, h6.trans hA53⟩

/-! ## 3. The THR words in consumer form -/

theorem srcB_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    ThrSelBase.srcB a r = (Request.thr r four L target).topWord a := by
  simp [ThrSelBase.srcB, Request.topWord, List.flatMap_map, PCJ45bee56da9f34d5a_TopChildCursor.payload]

section Ready
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ) (NI oT : ℕ) (h : 146 ≤ NI) (hT : 146 ≤ oT)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
  (A : Fin (2 + rowsWork NI) → List Bool)
  (hW : WordsAt a bnd ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU NI oT (.thr r four L target) A)

include hW in
/-- The 78 base-worker words. -/
theorem base_ready (k : Fin 82) (hk2 : ¬ (73 ≤ k.val ∧ k.val < 77)) :
    A (initPort NI (ib NI h k)) = ThrSelBase.baseInit a r four L target k := by
  obtain ⟨k, hk⟩ := k
  simp only at hk2
  interval_cases k
  · rw [show initPort NI (ib NI h ⟨0, by omega⟩) = wp NI (2 + uDst 0) from pw NI _ _ rfl, hW.2.2.2.1 ⟨0, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨0, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨1, by omega⟩) = wp NI (2 + uDst 1) from pw NI _ _ rfl, hW.2.2.2.1 ⟨1, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨1, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨2, by omega⟩) = wp NI (2 + wDst oT 6) from pw NI _ _ rfl, hW.1 ⟨6, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨2, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate ((12 * ThrWidth.T a r four L target + 17)) true)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨3, by omega⟩) = wp NI (2 + wDst oT 7) from pw NI _ _ rfl, hW.1 ⟨7, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨3, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (frame (SignedSortKey.binary (12 * ThrWidth.T a r four L target + 17) 0))) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨4, by omega⟩) = wp NI (2 + wDst oT 8) from pw NI _ _ rfl, hW.1 ⟨8, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨4, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate ((8 * (12 * ThrWidth.T a r four L target + 17) + 12)) true)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨5, by omega⟩) = wp NI (2 + uDst 2) from pw NI _ _ rfl, hW.2.2.2.1 ⟨2, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨5, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨6, by omega⟩) = wp NI (2 + wDst oT 9) from pw NI _ _ rfl, hW.1 ⟨9, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨6, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (RepairSource.VerifierDecoding.CompareMachine.word 0)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨7, by omega⟩) = wp NI (53) from pw NI _ _ rfl, hW.2.2.2.2.2]
    rw [show ThrSelBase.baseInit a r four L target ⟨7, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (0) true)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨8, by omega⟩) = wp NI (2 + wDst oT 10) from pw NI _ _ rfl, hW.1 ⟨10, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨8, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (((12 * ThrWidth.T a r four L target + 17) + 2)) true)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨9, by omega⟩) = wp NI (2 + uDst 66) from pw NI _ _ rfl, hW.2.2.2.1 ⟨66, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨9, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (frame (SignedSortKey.binary ((12 * ThrWidth.T a r four L target + 17) + 2) 1)))) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨10, by omega⟩) = wp NI (2 + uDst 3) from pw NI _ _ rfl, hW.2.2.2.1 ⟨3, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨10, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨11, by omega⟩) = wp NI (2 + uDst 4) from pw NI _ _ rfl, hW.2.2.2.1 ⟨4, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨11, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨12, by omega⟩) = wp NI (2 + uDst 5) from pw NI _ _ rfl, hW.2.2.2.1 ⟨5, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨12, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨13, by omega⟩) = wp NI (2 + uDst 6) from pw NI _ _ rfl, hW.2.2.2.1 ⟨6, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨13, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨14, by omega⟩) = wp NI (2 + uDst 7) from pw NI _ _ rfl, hW.2.2.2.1 ⟨7, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨14, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨15, by omega⟩) = wp NI (2 + uDst 8) from pw NI _ _ rfl, hW.2.2.2.1 ⟨8, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨15, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨16, by omega⟩) = wp NI (2 + uDst 9) from pw NI _ _ rfl, hW.2.2.2.1 ⟨9, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨16, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨17, by omega⟩) = wp NI (2 + uDst 10) from pw NI _ _ rfl, hW.2.2.2.1 ⟨10, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨17, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨18, by omega⟩) = wp NI (2 + uDst 11) from pw NI _ _ rfl, hW.2.2.2.1 ⟨11, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨18, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨19, by omega⟩) = wp NI (2 + uDst 12) from pw NI _ _ rfl, hW.2.2.2.1 ⟨12, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨19, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨20, by omega⟩) = wp NI (2 + uDst 13) from pw NI _ _ rfl, hW.2.2.2.1 ⟨13, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨20, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨21, by omega⟩) = wp NI (2 + uDst 14) from pw NI _ _ rfl, hW.2.2.2.1 ⟨14, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨21, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨22, by omega⟩) = wp NI (2 + uDst 15) from pw NI _ _ rfl, hW.2.2.2.1 ⟨15, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨22, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨23, by omega⟩) = wp NI (2 + uDst 16) from pw NI _ _ rfl, hW.2.2.2.1 ⟨16, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨23, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨24, by omega⟩) = wp NI (2 + uDst 17) from pw NI _ _ rfl, hW.2.2.2.1 ⟨17, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨24, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨25, by omega⟩) = wp NI (2 + uDst 18) from pw NI _ _ rfl, hW.2.2.2.1 ⟨18, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨25, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨26, by omega⟩) = wp NI (2 + uDst 19) from pw NI _ _ rfl, hW.2.2.2.1 ⟨19, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨26, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨27, by omega⟩) = wp NI (2 + uDst 20) from pw NI _ _ rfl, hW.2.2.2.1 ⟨20, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨27, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨28, by omega⟩) = wp NI (2 + uDst 21) from pw NI _ _ rfl, hW.2.2.2.1 ⟨21, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨28, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨29, by omega⟩) = wp NI (2 + uDst 22) from pw NI _ _ rfl, hW.2.2.2.1 ⟨22, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨29, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨30, by omega⟩) = wp NI (2 + uDst 23) from pw NI _ _ rfl, hW.2.2.2.1 ⟨23, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨30, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨31, by omega⟩) = wp NI (2 + uDst 24) from pw NI _ _ rfl, hW.2.2.2.1 ⟨24, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨31, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨32, by omega⟩) = wp NI (2 + uDst 25) from pw NI _ _ rfl, hW.2.2.2.1 ⟨25, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨32, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨33, by omega⟩) = wp NI (2 + uDst 26) from pw NI _ _ rfl, hW.2.2.2.1 ⟨26, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨33, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨34, by omega⟩) = wp NI (2 + uDst 27) from pw NI _ _ rfl, hW.2.2.2.1 ⟨27, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨34, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨35, by omega⟩) = wp NI (2 + uDst 28) from pw NI _ _ rfl, hW.2.2.2.1 ⟨28, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨35, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨36, by omega⟩) = wp NI (2 + uDst 29) from pw NI _ _ rfl, hW.2.2.2.1 ⟨29, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨36, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨37, by omega⟩) = wp NI (2 + uDst 30) from pw NI _ _ rfl, hW.2.2.2.1 ⟨30, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨37, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨38, by omega⟩) = wp NI (2 + uDst 31) from pw NI _ _ rfl, hW.2.2.2.1 ⟨31, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨38, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨39, by omega⟩) = wp NI (2 + uDst 32) from pw NI _ _ rfl, hW.2.2.2.1 ⟨32, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨39, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨40, by omega⟩) = wp NI (2 + uDst 33) from pw NI _ _ rfl, hW.2.2.2.1 ⟨33, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨40, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨41, by omega⟩) = wp NI (2 + uDst 34) from pw NI _ _ rfl, hW.2.2.2.1 ⟨34, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨41, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨42, by omega⟩) = wp NI (2 + uDst 35) from pw NI _ _ rfl, hW.2.2.2.1 ⟨35, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨42, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨43, by omega⟩) = wp NI (2 + uDst 36) from pw NI _ _ rfl, hW.2.2.2.1 ⟨36, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨43, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨44, by omega⟩) = wp NI (2 + uDst 37) from pw NI _ _ rfl, hW.2.2.2.1 ⟨37, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨44, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨45, by omega⟩) = wp NI (2 + uDst 38) from pw NI _ _ rfl, hW.2.2.2.1 ⟨38, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨45, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨46, by omega⟩) = wp NI (2 + uDst 39) from pw NI _ _ rfl, hW.2.2.2.1 ⟨39, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨46, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨47, by omega⟩) = wp NI (2 + uDst 40) from pw NI _ _ rfl, hW.2.2.2.1 ⟨40, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨47, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨48, by omega⟩) = wp NI (2 + uDst 41) from pw NI _ _ rfl, hW.2.2.2.1 ⟨41, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨48, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨49, by omega⟩) = wp NI (2 + uDst 42) from pw NI _ _ rfl, hW.2.2.2.1 ⟨42, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨49, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨50, by omega⟩) = wp NI (2 + uDst 43) from pw NI _ _ rfl, hW.2.2.2.1 ⟨43, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨50, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨51, by omega⟩) = wp NI (2 + uDst 44) from pw NI _ _ rfl, hW.2.2.2.1 ⟨44, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨51, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨52, by omega⟩) = wp NI (2 + uDst 45) from pw NI _ _ rfl, hW.2.2.2.1 ⟨45, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨52, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨53, by omega⟩) = wp NI (2 + uDst 46) from pw NI _ _ rfl, hW.2.2.2.1 ⟨46, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨53, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨54, by omega⟩) = wp NI (2 + wDst oT 23) from pw NI _ _ rfl, hW.1 ⟨23, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨54, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) true)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨55, by omega⟩) = wp NI (101) from pw NI _ _ rfl, hW.2.2.2.2.1]
    rw [show ThrSelBase.baseInit a r four L target ⟨55, by omega⟩ = ZeroPadding.pad 0 (ZeroPadding.pad 0 (List.replicate ((ThrSelBase.bU (ThrWidth.T a r four L target) + 1)) false)) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨56, by omega⟩) = wp NI (2 + uDst 47) from pw NI _ _ rfl, hW.2.2.2.1 ⟨47, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨56, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨57, by omega⟩) = wp NI (2 + uDst 48) from pw NI _ _ rfl, hW.2.2.2.1 ⟨48, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨57, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) [] from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨58, by omega⟩) = wp NI (2 + uDst 49) from pw NI _ _ rfl, hW.2.2.2.1 ⟨49, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨58, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨59, by omega⟩) = wp NI (2 + uDst 50) from pw NI _ _ rfl, hW.2.2.2.1 ⟨50, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨59, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨60, by omega⟩) = wp NI (2 + uDst 51) from pw NI _ _ rfl, hW.2.2.2.1 ⟨51, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨60, by omega⟩ = List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨61, by omega⟩) = wp NI (2 + uDst 52) from pw NI _ _ rfl, hW.2.2.2.1 ⟨52, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨61, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨62, by omega⟩) = wp NI (2 + uDst 53) from pw NI _ _ rfl, hW.2.2.2.1 ⟨53, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨62, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨63, by omega⟩) = wp NI (2 + uDst 54) from pw NI _ _ rfl, hW.2.2.2.1 ⟨54, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨63, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨64, by omega⟩) = wp NI (2 + uDst 55) from pw NI _ _ rfl, hW.2.2.2.1 ⟨55, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨64, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨65, by omega⟩) = wp NI (2 + uDst 56) from pw NI _ _ rfl, hW.2.2.2.1 ⟨56, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨65, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨66, by omega⟩) = wp NI (2 + uDst 57) from pw NI _ _ rfl, hW.2.2.2.1 ⟨57, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨66, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨67, by omega⟩) = wp NI (2 + uDst 58) from pw NI _ _ rfl, hW.2.2.2.1 ⟨58, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨67, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨68, by omega⟩) = wp NI (2 + uDst 59) from pw NI _ _ rfl, hW.2.2.2.1 ⟨59, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨68, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨69, by omega⟩) = wp NI (2 + uDst 60) from pw NI _ _ rfl, hW.2.2.2.1 ⟨60, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨69, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨70, by omega⟩) = wp NI (2 + uDst 61) from pw NI _ _ rfl, hW.2.2.2.1 ⟨61, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨70, by omega⟩ = ZeroPadding.pad 0 (List.replicate (ThrSelBase.bU (ThrWidth.T a r four L target)) false) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨71, by omega⟩) = wp NI (2 + wDst oT 11) from pw NI _ _ rfl, hW.1 ⟨11, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨71, by omega⟩ = frame (ThrSelBase.srcB a r) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨72, by omega⟩) = wp NI (2 + wDst oT 12) from pw NI _ _ rfl, hW.1 ⟨12, by decide⟩ (Or.inl (by decide))]
    rw [show ThrSelBase.baseInit a r four L target ⟨72, by omega⟩ = List.replicate ((ThrWidth.T a r four L target)) true from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · exact absurd ⟨by omega, by omega⟩ hk2
  · exact absurd ⟨by omega, by omega⟩ hk2
  · exact absurd ⟨by omega, by omega⟩ hk2
  · exact absurd ⟨by omega, by omega⟩ hk2
  · rw [show initPort NI (ib NI h ⟨77, by omega⟩) = wp NI (2 + uDst 62) from pw NI _ _ rfl, hW.2.2.2.1 ⟨62, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨77, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (RepairSource.VerifierDecoding.CompareMachine.word 0) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨78, by omega⟩) = wp NI (2 + uDst 63) from pw NI _ _ rfl, hW.2.2.2.1 ⟨63, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨78, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (RepairSource.VerifierDecoding.CompareMachine.word 1) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨79, by omega⟩) = wp NI (2 + uDst 64) from pw NI _ _ rfl, hW.2.2.2.1 ⟨64, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨79, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (RepairSource.VerifierDecoding.CompareMachine.word 2) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨80, by omega⟩) = wp NI (2 + uDst 65) from pw NI _ _ rfl, hW.2.2.2.1 ⟨65, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨80, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (RepairSource.VerifierDecoding.CompareMachine.word 3) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]
  · rw [show initPort NI (ib NI h ⟨81, by omega⟩) = wp NI (2 + uDst 68) from pw NI _ _ rfl, hW.2.2.2.1 ⟨68, by decide⟩]
    rw [show ThrSelBase.baseInit a r four L target ⟨81, by omega⟩ = ZeroPadding.pad (ThrSelBase.bU (ThrWidth.T a r four L target)) (UnaryTemplate.tape r.circuits.length) from rfl]
    simp [thrInitWord, selU, dataU, pad_nil, uDst, wDst, srcB_eq a r four L target, ThrSelBase.bU, ThrWidth.T, RowsInit.LoopFan.circOf]

theorem rp_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    PrimeReserve.rpOf a (.thr r four L target) = rpVal a (.thr r four L target) := rfl

include hW in
/-- **`ThrC5Ready`** at the fixed index maps and RW's prime reserve `rpOf a`. -/
theorem thr_c5 (hbnd : ∀ c, bnd (.thr r four L target) c = ThrSel.bnd a r c) :
    PartsStep.ThrC5Ready a r four L target NI (fun i => A (initPort NI i)) (iMode NI h) (ini NI h) (ix NI h)
      (ib NI h) (iOne NI h) (PrimeReserve.rpOf a (.thr r four L target)) := by
  have hb := base_ready a bnd NI oT h r four L target A hW
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  refine ⟨?_, ini_inj NI h, fun m => ?_, ib_inj NI h, ib9_ne NI h, fun c => ?_, hb, ?_⟩ <;> beta_reduce
  · rw [show initPort NI (iMode NI h) = wp NI (2 + wDst oT 30) from pw NI _ _ rfl, h1 ⟨30, by decide⟩ (Or.inr rfl)]
    rfl
  · obtain ⟨m, hm⟩ := m
    rw [rp_eq]
    by_cases m0 : m = 0
    · subst m0
      rw [show initPort NI (ini NI h ⟨0, hm⟩) = wp NI (2 + wDst oT 0) from pw NI _ _ rfl,
        h1 ⟨0, by decide⟩ (Or.inl (by decide))]
      rfl
    by_cases m1 : m = 1
    · subst m1
      rw [show initPort NI (ini NI h ⟨1, hm⟩) = wp NI (2 + wDst oT 1) from pw NI _ _ rfl,
        h1 ⟨1, by decide⟩ (Or.inl (by decide))]
      rfl
    by_cases m38 : m = 38
    · subst m38
      rw [show initPort NI (ini NI h ⟨38, hm⟩) = wp NI 40 from pw NI _ _ rfl, h3]
      rfl
    by_cases m39 : m = 39
    · subst m39
      rw [show initPort NI (ini NI h ⟨39, hm⟩) = wp NI (2 + wDst oT 22) from pw NI _ _ rfl,
        h1 ⟨22, by decide⟩ (Or.inl (by decide))]
      rfl
    rw [show initPort NI (ini NI h ⟨m, hm⟩) = wp NI (4 + (m - 2)) from pw NI _ _ (by simp only [ini]; omega),
      h2 (m - 2) (by omega)]
    simp only [ThrKey.psInit, if_neg m0, if_neg m1, if_neg m38, if_neg m39]
  · obtain ⟨c, hc⟩ := c
    rw [show initPort NI (ix NI h ⟨c, hc⟩) = wp NI (2 + wDst oT (c + 2)) from pw NI _ _ (by
        simp only [ix]; interval_cases c <;> rfl),
      h1 ⟨c + 2, by omega⟩ (Or.inl (by simp only; omega))]
    interval_cases c <;> (simp only [thrInitWord]; rw [hbnd]; rfl)
  · rw [show initPort NI (iOne NI h) = wp NI (2 + uDst 67) from pw NI _ _ rfl, h4 ⟨67, by decide⟩]
    simp [selU, dataU, thrInitWord, ThrSelBase.bU, ThrWidth.T, KeyStep.fb]

include hW in
/-- **`K0Ready`'s `iz` words** (`thrZInit wT T F U`). -/
theorem thr_iz (m : Fin 9) :
    A (initPort NI (iz NI h m)) = KeyZeroThr.thrZInit (KeyTop.wT a r four L target) (ThrWidth.T a r four L target)
      (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target)) m := by
  obtain ⟨h1, -, -, -, -, -⟩ := hW
  obtain ⟨m, hm⟩ := m
  rw [show initPort NI (iz NI h ⟨m, hm⟩) = wp NI (2 + wDst oT (13 + m)) from pw NI _ _ (by
      simp only [iz]; interval_cases m <;> rfl),
    h1 ⟨13 + m, by omega⟩ (Or.inl (by simp only; omega))]
  interval_cases m <;> rfl

end Ready

end
end RowsInit.ThrInitReady
