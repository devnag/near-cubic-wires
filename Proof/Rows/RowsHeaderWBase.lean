import Proof.Rows.RowsInitHdrSpec
import Proof.Rows.RowsInitHeaderRadix
import Proof.Rows.RowsInitVecDock

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsHeaderW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.PacketsGlue.RequestMeta
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)

/-! ## 1. The two request-level values and the typed Header-282 stage -/

/-- Header 15's value: the byte length of the pool's decomposition cache word, plus one (RW's `b15`). -/
def b15 (r : Request) : ℕ :=
  (exactListWord (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a
    (Packets.live (r.family a)) (r.family a).occurrences)).length + 1

/-- `N`, the pool length (Header 4 = `UnaryTemplate.tape N`). -/
def poolN (r : Request) : ℕ := (Packets.pool a (r.family a) (geometryOf selector a r)).length

/-- The Header-282 stage's entry bank: framed request (0), metadata word (1), `tape N` (2), else blank. -/
def h282In (e : ℕ) (x m t : List Bool) : Fin (4 + e) → List Bool := fun i =>
  if i.val = 0 then x else if i.val = 1 then m else if i.val = 2 then t else []

/-- **Header 282's producer, typed.** One fixed machine; heads `0 → 0`; the three inputs kept; tape 3 =
`UnaryTemplate.tape (min degree N)`; cost a fixed power of `smallSize` plus the metadata length. -/
structure H282Spec where
  extra : ℕ
  states : ℕ
  machine : Machine (4 + extra) states
  cost : Request → ℕ → ℕ → ℕ → RowCaps → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ (r : Request) (w deg C : ℕ) (caps : RowCaps), cost r w deg C caps ≤
    coefficient * ((r.smallSize a) ^ degree + (rowMetadataWord w deg C caps).length + 1)
  run : ∀ (r : Request) (w deg C : ℕ) (caps : RowCaps), ∃ A' : Fin (4 + extra) → List Bool,
    Step machine (cost r w deg C caps) (fun _ => 0)
      (h282In extra (frame (r.input a)) (rowMetadataWord w deg C caps) (UnaryTemplate.tape (poolN selector a r)))
      (fun _ => 0) A' ∧
    A' ⟨0, by omega⟩ = frame (r.input a) ∧ A' ⟨1, by omega⟩ = rowMetadataWord w deg C caps ∧
    A' ⟨2, by omega⟩ = UnaryTemplate.tape (poolN selector a r) ∧
    A' ⟨3, by omega⟩ = UnaryTemplate.tape (min deg (poolN selector a r))

/-! ## 2. The metadata unwrap -/

/-- The row metadata word is the frame of `RowsInit.metaWord` (as `Entry` unwraps it). -/
theorem unwrap_meta (w deg C : ℕ) (caps : RowCaps) :
    rowMetadataWord w deg C caps =
      frame (RowsInit.metaWord w deg C caps.headerFuel caps.copyCap caps.descriptorReserve caps.rawReserve) := rfl

theorem unwrap_run (m : List Bool) : ∃ A : Fin (2 + 1) → List Bool,
    Step (MaskedReset.machine GeneratedAmplifier.Copy.machine (fun _ => true)) (2 * (2 * m.length + 1) + 2)
      (fun _ => 0) (Fin.addCases (m := 2) (n := 1) ![frame m, []] (fun _ => [])) (fun _ => 0) A ∧
    A 0 = frame m ∧ A 1 = m := by
  obtain ⟨r, hr, hf, hs⟩ := GeneratedAmplifier.Copy.copy_run [] m [] []
  have h : Step GeneratedAmplifier.Copy.machine (2 * m.length + 1) ![0, 0] ![frame m ++ [], []]
      ![([] : List Bool).length + 2 * m.length + 1, ([] ++ m).length] ![frame m ++ [], m] :=
    ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩
  rw [List.append_nil] at h
  obtain ⟨k, -, mk⟩ := RowsInit.mask_empty h (fun _ => true) (fun i _ => by fin_cases i <;> rfl)
  rw [RowsInit.vec2_zero] at mk
  have hk := (mk.congr_in (RowsInit.zeros_addCases _ _) rfl).congr (RowsInit.zeros_masked _) rfl
  refine ⟨_, hk, ?_, ?_⟩
  · show Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool) ![frame m, m]
      (fun _ => List.replicate k false) (Fin.castAdd 1 0) = _
    rw [Fin.addCases_left]
    rfl
  · show Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool) ![frame m, m]
      (fun _ => List.replicate k false) (Fin.castAdd 1 1) = _
    rw [Fin.addCases_left]
    rfl

theorem frame_length (m : List Bool) : (frame m).length = 2 * m.length + 1 := by
  simp

/-! ## 3. Header 262 -/

/-- **Header 262 of the entry Header block is the request's raw word** (the public input's, unchanged). -/
theorem common_262 (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) :
    PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) (geometryOf selector a r) layout 262 = r.raw selector a := by
  unfold PCJ45bee56da9f34d5a_RowState.commonHeader CompactNativeInitialize.input
  rw [install_other _ _ _ _ (fun j => by revert j; decide)]
  simp only [CompactNativeInitialize.base, if_neg (by decide : (262 : Fin 440) ≠ 180), ↓reduceIte]
  rfl

/-! ## 4. The local bank and its slot maps -/

/-- Scratch size: `Fin (444 + needH e p)` has room for the six stages (`e`, `p` = the Header-15/282 stages' extras). -/
def needH (e p : ℕ) : ℕ := 102 + e + p

def uMap (i : ℕ) : ℕ := if i = 0 then 441 else 443 + i
def lMap (i : ℕ) : ℕ :=
  if i = 0 then 440 else if i = 62 then 3 else if i = 68 then 283 else if i = 71 then 277 else 445 + i
def aMap (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 3 else if i = 2 then 444 else if i = 12 then 4 else if i = 16 then 278
  else if i = 26 then 88 else 515 + i
def fMap (i : ℕ) : ℕ := if i = 0 then 440 else if i = 1 then 15 else 543 + i
def pMap (e i : ℕ) : ℕ := if i = 0 then 440 else if i = 1 then 441 else if i = 2 then 4 else if i = 3 then 282 else 542 + e + i

/-- The value ranges each stage writes (for the frame facts). -/
def RU (v : ℕ) : Prop := v = 441 ∨ v = 444 ∨ v = 445
def RL (v : ℕ) : Prop := v = 440 ∨ v = 3 ∨ v = 283 ∨ v = 277 ∨ (446 ≤ v ∧ v ≤ 517)
def RA (v : ℕ) : Prop := v = 0 ∨ v = 3 ∨ v = 444 ∨ v = 4 ∨ v = 278 ∨ v = 88 ∨ (518 ≤ v ∧ v ≤ 544)
def RF (e v : ℕ) : Prop := v = 440 ∨ v = 15 ∨ (545 ≤ v ∧ v ≤ 545 + e)
def RP (e p v : ℕ) : Prop := v = 440 ∨ v = 441 ∨ v = 4 ∨ v = 282 ∨ (546 + e ≤ v ∧ v ≤ 545 + e + p)

theorem uMap_range (i : ℕ) (h : i < 3) : RU (uMap i) := by
  unfold RU uMap; split_ifs <;> omega
theorem lMap_range (i : ℕ) (h : i < 73) : RL (lMap i) := by
  unfold RL lMap; split_ifs <;> omega
theorem aMap_range (i : ℕ) (h : i < 30) : RA (aMap i) := by
  unfold RA aMap; split_ifs <;> omega
theorem fMap_range (e i : ℕ) (h : i < 2 + e + 1) : RF e (fMap i) := by
  unfold RF fMap; split_ifs <;> omega
theorem pMap_range (e p i : ℕ) (h : i < 4 + p) : RP e p (pMap e i) := by
  unfold RP pMap; split_ifs <;> omega

variable (e p : ℕ)

def slU : Fin (2 + 1) → Fin (440 + 4 + needH e p) := fun i =>
  ⟨uMap i.val, by have := uMap_range i.val i.isLt; unfold RU at this; unfold needH; omega⟩
def slL : Fin 73 → Fin (440 + 4 + needH e p) := fun i =>
  ⟨lMap i.val, by have := lMap_range i.val i.isLt; unfold RL at this; unfold needH; omega⟩
def slA : Fin 30 → Fin (440 + 4 + needH e p) := fun i =>
  ⟨aMap i.val, by have := aMap_range i.val i.isLt; unfold RA at this; unfold needH; omega⟩
def slF : Fin (2 + e + 1) → Fin (440 + 4 + needH e p) := fun i =>
  ⟨fMap i.val, by have := fMap_range e i.val i.isLt; unfold RF at this; unfold needH; omega⟩
def slP : Fin (4 + p) → Fin (440 + 4 + needH e p) := fun i =>
  ⟨pMap e i.val, by have := pMap_range e p i.val i.isLt; unfold RP at this; unfold needH; omega⟩
/-- The Header block of the local bank. -/
def hdrP : Fin 440 → Fin (440 + 4 + needH e p) := fun k => ⟨k.val, by unfold needH; omega⟩

theorem slU_inj : Function.Injective (slU e p) := by
  intro i j h
  have hv : uMap i.val = uMap j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold uMap at hv
  split_ifs at hv <;> omega

theorem slL_inj : Function.Injective (slL e p) := by
  intro i j h
  have hv : lMap i.val = lMap j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold lMap at hv
  split_ifs at hv <;> omega

theorem slA_inj : Function.Injective (slA e p) := by
  intro i j h
  have hv : aMap i.val = aMap j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold aMap at hv
  split_ifs at hv <;> omega

theorem slF_inj : Function.Injective (slF e p) := by
  intro i j h
  have hv : fMap i.val = fMap j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold fMap at hv
  split_ifs at hv <;> omega

theorem slP_inj : Function.Injective (slP e p) := by
  intro i j h
  have hv : pMap e i.val = pMap e j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold pMap at hv
  split_ifs at hv <;> omega

theorem hdrP_inj : Function.Injective (hdrP e p) := by
  intro i j h
  have hv : (hdrP e p i).val = (hdrP e p j).val := congrArg Fin.val h
  exact Fin.ext hv

/-- The erase map of the 430 mutable Header ports, driver 442, log 443. -/
def slR : Fin (430 + 1 + 1) → Fin (440 + 4 + needH e p) :=
  RowsInit.eraseAll (fun i => hdrP e p (PCJ45bee56da9f34d5a_HeaderErase.mutable i))
    ⟨442, by unfold needH; omega⟩ ⟨443, by unfold needH; omega⟩

theorem slR_inj : Function.Injective (slR e p) := by
  refine RowsInit.eraseAll_injective _ _ _ (fun i j h => PCJ45bee56da9f34d5a_HeaderErase.mutable_injective
    (hdrP_inj e p h)) (fun i h => ?_) (fun i h => ?_) (fun h => ?_)
  · have hv := congrArg Fin.val h
    have := (PCJ45bee56da9f34d5a_HeaderErase.mutable i).isLt
    simp only [hdrP] at hv
    omega
  · have hv := congrArg Fin.val h
    have := (PCJ45bee56da9f34d5a_HeaderErase.mutable i).isLt
    simp only [hdrP] at hv
    omega
  · have hv := congrArg Fin.val h
    simp at hv

/-- The erase map's ports are the mutable Header ports, 442 and 443: never a retained Header port. -/
theorem slR_val (i : Fin (430 + 1 + 1)) :
    (∃ j : Fin 430, (slR e p i).val = (PCJ45bee56da9f34d5a_HeaderErase.mutable j).val) ∨
      (slR e p i).val = 442 ∨ (slR e p i).val = 443 := by
  refine Fin.addCases (m := 430 + 1) (n := 1) (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (m := 430) (n := 1) (fun j => ?_) (fun j => ?_) i
    · left
      refine ⟨j, ?_⟩
      simp only [slR, RowsInit.eraseAll, Fin.addCases_left]
      rfl
    · right; left
      simp only [slR, RowsInit.eraseAll, Fin.addCases_left, Fin.addCases_right]
  · right; right
    simp only [slR, RowsInit.eraseAll, Fin.addCases_right]

/-- A port whose value avoids a stage's range is not one of its slots. -/
theorem not_hit {t T : ℕ} (sl : Fin t → Fin T) (R : ℕ → Prop) (hR : ∀ j, R (sl j).val) (x : Fin T)
    (hx : ¬ R x.val) : ∀ j, sl j ≠ x := fun j h => hx (h ▸ hR j)

theorem slU_range (j : Fin (2 + 1)) : RU (slU e p j).val := uMap_range j.val j.isLt
theorem slL_range (j : Fin 73) : RL (slL e p j).val := lMap_range j.val j.isLt
theorem slA_range (j : Fin 30) : RA (slA e p j).val := aMap_range j.val j.isLt
theorem slF_range (j : Fin (2 + e + 1)) : RF e (slF e p j).val := fMap_range e j.val j.isLt
theorem slP_range (j : Fin (4 + p)) : RP e p (slP e p j).val := pMap_range e p j.val j.isLt

end
end RowsHeaderW
