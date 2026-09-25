import Proof.Rows.RowsInitVecDock

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.ThrLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.VecDock RowsInit.LoopFan RowsInit.MasterFan PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
noncomputable section

/-! ## 1. Work ports by value -/

theorem rw_eq (NI : ℕ) : rowsWork NI = NI + 610 := rfl

/-- The work port of value `v` (clamped; every use has `v < 2 + rowsWork NI`). -/
def wp (NI v : ℕ) : Fin (2 + rowsWork NI) := ⟨v % (2 + rowsWork NI), Nat.mod_lt _ (by omega)⟩

theorem wp_val {NI v : ℕ} (h : v < 2 + rowsWork NI) : (wp NI v).val = v := Nat.mod_eq_of_lt h

theorem pub_val (NI : ℕ) (i : Fin 2) : (pubPort NI i).val = i.val := rfl
theorem init_val (NI : ℕ) (i : Fin NI) : (initPort NI i).val = 2 + i.val := by
  simp [initPort] <;> omega
theorem loop_val (NI : ℕ) (i : Fin (MT+1+1)) : (loopPort NI i).val = 2 + NI + 72 + i.val := by
  simp [loopPort, fixPort, MT] <;> omega
theorem c6_val (NI : ℕ) (i : Fin 2) : (c6Port NI i).val = 2 + NI + 592 + i.val := by
  simp [c6Port, fixPort, MT] <;> omega
theorem master_val (NI : ℕ) (k : Fin 254) : (masterPort NI k).val = 2 + NI + 329 + k.val := by
  simp [masterPort, loopPort, fixPort, masterP, CellReload.masterPort, MT] <;> omega

/-- A slot map given by a value function. -/
def vmap (NI n : ℕ) (f : ℕ → ℕ) : Fin n → Fin (2 + rowsWork NI) := fun i => wp NI (f i.val)

theorem vmap_val {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI) (i : Fin n) :
    (vmap NI n f i).val = f i.val := wp_val (hb i.val i.isLt)

theorem vmap_inj {NI n : ℕ} {f : ℕ → ℕ} (hb : ∀ v, v < n → f v < 2 + rowsWork NI)
    (hf : ∀ v w, v < n → w < n → f v = f w → v = w) : Function.Injective (vmap NI n f) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [vmap_val hb, vmap_val hb] at hv
  exact Fin.ext (hf _ _ i.isLt j.isLt hv)

/-- A port outside a stage's value range keeps its content. -/
theorem inst_out {t u : ℕ} (sl : Fin t → Fin u) (A : Fin u → List Bool) (B : Fin t → List Bool) (x : Fin u)
    (P : ℕ → Prop) (hP : ∀ j, P (sl j).val) (hx : ¬ P x.val) : install sl A B x = A x :=
  install_other _ _ _ _ (fun j h => hx (h ▸ hP j))

/-! ## 2. The four slot maps (init region `[o, o + need a)`) -/

/-- The ten THR key masters, as a predicate on the master index. -/
def isKey (k : ℕ) : Prop :=
  k = 149 ∨ k = 209 ∨ k = 218 ∨ k = 220 ∨ k = 228 ∨ k = 229 ∨ k = 230 ∨ k = 231 ∨ k = 240 ∨ k = 242

instance (k : ℕ) : Decidable (isKey k) := by unfold isKey; infer_instance

theorem isKey_iff (k : Fin 254) : isKey k.val ↔ k ∈ thrKeySet := by
  unfold isKey thrKeySet
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  rfl

/-- The init ports the block uses: sources 23, junk 254, table inputs 3, and the three stages' scratch. -/
def need (a : DecompositionAlgorithm) : ℕ := 344 + (RowsInit.LoopWords.loopVec a).extra + (RowsInit.LoopAux.auxVec a).extra

/-- `loopVec`: request (pub 0), sources (init `o..o+22`), clock (loop cell 254), scratch (init `o+280..`). -/
def f1 (NI o v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 23 then 2 + o + (v - 1) else if v = 24 then 2 + NI + 326 else 2 + o + 280 + (v - 25)

/-- The fanout: sources, 254 cells, 254 masters (key ones to junk init `o+23+k`), aux 2, clock, log. -/
def fF (NI o v : ℕ) : ℕ :=
  if v < 23 then 2 + o + v else if v < 277 then 2 + NI + 72 + (v - 23)
  else if v < 531 then (if isKey (v - 277) then 2 + o + 23 + (v - 277) else 2 + NI + 329 + (v - 277))
  else if v = 531 then 2 + NI + 585 else if v = 532 then 2 + NI + 326 else 2 + NI + 327

/-- `auxVec`: request, aux 0,1,3,4,5,6, table inputs (init `o+277..279`), scratch (init `o+281+E1..`). -/
def f3 (NI o e1 v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 2 then 2 + NI + 582 + v else if v ≤ 6 then 2 + NI + 583 + v
  else if v ≤ 9 then 2 + o + 270 + v else 2 + o + 271 + e1 + v

/-- The table stage: inputs, counters (loop 518, 519), C6, verdict (cell 256), scratch (init `o+282+E1+E2..`). -/
def f4 (NI o e1 e2 v : ℕ) : ℕ :=
  if v ≤ 2 then 2 + o + 277 + v else if v = 3 then 2 + NI + 590 else if v = 4 then 2 + NI + 591
  else if v = 5 then 2 + NI + 592 else if v = 6 then 2 + NI + 593 else if v = 7 then 2 + NI + 328
  else 2 + o + 274 + e1 + e2 + v

def sl1 (a : DecompositionAlgorithm) (NI o : ℕ) := vmap NI (1 + 24 + (RowsInit.LoopWords.loopVec a).extra + 1) (f1 NI o)
def slF (NI o : ℕ) := vmap NI (23 + (509 + 1) + 1) (fF NI o)
def sl3 (a : DecompositionAlgorithm) (NI o : ℕ) := vmap NI (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1) (f3 NI o ((RowsInit.LoopWords.loopVec a).extra))
def sl4 (a : DecompositionAlgorithm) (NI o : ℕ) := vmap NI (RowsInit.LoopTable.N + 1) (f4 NI o ((RowsInit.LoopWords.loopVec a).extra) ((RowsInit.LoopAux.auxVec a).extra))

section Maps
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem b1 : ∀ v, v < 1 + 24 + (RowsInit.LoopWords.loopVec a).extra + 1 → f1 NI o v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f1; split_ifs <;> omega
theorem bF : ∀ v, v < 23 + (509 + 1) + 1 → fF NI o v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold fF; split_ifs <;> omega
theorem b3 : ∀ v, v < 1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1 → f3 NI o ((RowsInit.LoopWords.loopVec a).extra) v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f3; split_ifs <;> omega
theorem b4 : ∀ v, v < RowsInit.LoopTable.N + 1 → f4 NI o ((RowsInit.LoopWords.loopVec a).extra) ((RowsInit.LoopAux.auxVec a).extra) v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f4 RowsInit.LoopTable.N at *; split_ifs <;> omega

theorem inj1 : Function.Injective (sl1 a NI o) := vmap_inj (b1 a NI o hNI) (by
  intro v w hv hw h; unfold need at hNI; unfold f1 at h; split_ifs at h <;> omega)
theorem injF : Function.Injective (slF NI o) := vmap_inj (bF a NI o hNI) (by
  intro v w hv hw h; unfold need at hNI; unfold fF at h; split_ifs at h <;> unfold isKey at * <;> omega)
theorem inj3 : Function.Injective (sl3 a NI o) := vmap_inj (b3 a NI o hNI) (by
  intro v w hv hw h; unfold need at hNI; unfold f3 at h; split_ifs at h <;> omega)
theorem inj4 : Function.Injective (sl4 a NI o) := vmap_inj (b4 a NI o hNI) (by
  intro v w hv hw h; unfold need at hNI; unfold f4 RowsInit.LoopTable.N at *; split_ifs at h <;> omega)

end Maps

/-! ## 3. Value ranges of the four stages -/

def R1 (NI o e1 v : ℕ) : Prop :=
  v = 0 ∨ (2 + o ≤ v ∧ v < 2 + o + 23) ∨ v = 2 + NI + 326 ∨ (2 + o + 280 ≤ v ∧ v ≤ 2 + o + 280 + e1)
def RF (NI o v : ℕ) : Prop :=
  (2 + o ≤ v ∧ v < 2 + o + 277) ∨ (2 + NI + 72 ≤ v ∧ v < 2 + NI + 328) ∨
  (2 + NI + 329 ≤ v ∧ v < 2 + NI + 583 ∧ ¬ isKey (v - (2 + NI + 329))) ∨ v = 2 + NI + 585
def R3 (NI o e1 e2 v : ℕ) : Prop :=
  v = 0 ∨ (2 + NI + 583 ≤ v ∧ v ≤ 2 + NI + 589 ∧ v ≠ 2 + NI + 585) ∨ (2 + o + 277 ≤ v ∧ v ≤ 2 + o + 279) ∨
  (2 + o + 281 + e1 ≤ v ∧ v ≤ 2 + o + 281 + e1 + e2)
def R4 (NI o e1 e2 v : ℕ) : Prop :=
  (2 + o + 277 ≤ v ∧ v ≤ 2 + o + 279) ∨ (2 + NI + 590 ≤ v ∧ v ≤ 2 + NI + 593) ∨ v = 2 + NI + 328 ∨
  (2 + o + 282 + e1 + e2 ≤ v ∧ v ≤ 2 + o + 343 + e1 + e2)

section Ranges
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem r1 : ∀ j, R1 NI o ((RowsInit.LoopWords.loopVec a).extra) (sl1 a NI o j).val := by
  intro j; have := j.isLt; unfold sl1; rw [vmap_val (b1 a NI o hNI)]; unfold R1 f1; split_ifs <;> omega
theorem rF : ∀ j, RF NI o (slF NI o j).val := by
  intro j; have := j.isLt; unfold slF; rw [vmap_val (bF a NI o hNI)]; unfold RF fF
  split_ifs with h1 h2 h3 h4 <;> first | omega | (right; right; left; refine ⟨by omega, by omega, ?_⟩; rwa [show 2 + NI + 329 + (j.val - 277) - (2 + NI + 329) = j.val - 277 by omega])
theorem r3 : ∀ j, R3 NI o ((RowsInit.LoopWords.loopVec a).extra) ((RowsInit.LoopAux.auxVec a).extra) (sl3 a NI o j).val := by
  intro j; have := j.isLt; unfold sl3; rw [vmap_val (b3 a NI o hNI)]; unfold R3 f3; split_ifs <;> omega
theorem r4 : ∀ j, R4 NI o ((RowsInit.LoopWords.loopVec a).extra) ((RowsInit.LoopAux.auxVec a).extra) (sl4 a NI o j).val := by
  intro j; have := j.isLt; unfold sl4; rw [vmap_val (b4 a NI o hNI)]; unfold R4 f4 RowsInit.LoopTable.N at *; split_ifs <;> omega

end Ranges

/-! ## 4. The machine and its cost -/

def m1 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl1 a NI o) (MaskedReset.machine (RowsInit.LoopWords.loopVec a).machine (fun _ => true))
def mF (NI o : ℕ) := RecoveryFocus.machine (slF NI o) (ExtIncidence.NativeFanout.machine fanSel)
def m3 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl3 a NI o) (MaskedReset.machine (RowsInit.LoopAux.auxVec a).machine (fun _ => true))
def m4 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl4 a NI o) (MaskedReset.machine RowsInit.LoopTable.machine (fun _ => true))

/-- **The THR loop-block writer** (one fixed machine per `a`, `NI`, `o`). -/
def machine (a : DecompositionAlgorithm) (NI o : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (m1 a NI o) (mF NI o)) (m3 a NI o)) (m4 a NI o)

/-- Its cost at a request. -/
def cost (a : DecompositionAlgorithm) (r : PCJd4d1d9d7d1fa4313_Production.Request) : ℕ :=
  (((2 * (RowsInit.LoopWords.loopVec a).cost r + 2) + 1 + (2 * thrRes r.q (r.input a).length + 4)) + 1 +
    (2 * (RowsInit.LoopAux.auxVec a).cost r + 2)) + 1 + (2 * RowsInit.LoopTable.tableCost (RowsInit.complCount a r) + 2)

/-! ## 5. The four stages -/

section Stages

end Stages

theorem sl1_zero (a : DecompositionAlgorithm) (NI o : ℕ) : sl1 a NI o ⟨0, by omega⟩ = pubPort NI 0 :=
  Fin.ext (by show (0 % (2 + rowsWork NI)) = 0; exact Nat.zero_mod _)

theorem sl1_src (a : DecompositionAlgorithm) (NI o : ℕ) (j : Fin 23) :
    sl1 a NI o ⟨j.val + 1, by omega⟩ = wp NI (2 + o + j.val) := by
  show wp NI (f1 NI o (j.val + 1)) = _
  have hj := j.isLt
  have e : f1 NI o (j.val + 1) = 2 + o + j.val := by
    unfold f1
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  rw [e]

theorem sl1_clock (a : DecompositionAlgorithm) (NI o : ℕ) : sl1 a NI o ⟨24, by omega⟩ = wp NI (2 + NI + 326) := by
  show wp NI (f1 NI o 24) = _
  congr 1

section Stages2
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

/-- **Stage 1** (`loopVec`, masked): sources on init `o..o+22`, clock `1^R` on loop cell 254. -/
theorem st1 (r : PCJd4d1d9d7d1fa4313_Production.Request) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a r))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ B : Fin (1 + 24 + (RowsInit.LoopWords.loopVec a).extra + 1) → List Bool,
      Step (m1 a NI o) (2 * (RowsInit.LoopWords.loopVec a).cost r + 2) (fun _ => 0) A (fun _ => 0)
        (install (sl1 a NI o) A B) ∧
      B ⟨0, by omega⟩ = frame (Request.input a r) ∧
      (∀ j : Fin 23, B ⟨j.val + 1, by omega⟩ = srcOf a r j) ∧
      B ⟨24, by omega⟩ = List.replicate (thrRes r.q (r.input a).length) true := by
  have hb := b1 a NI o hNI
  obtain ⟨B, hs, b0, bj⟩ := vec_dock (RowsInit.LoopWords.loopVec a) r (sl1 a NI o) (inj1 a NI o hNI) (fun _ => 0) A
    (fun _ => rfl) (by rw [sl1_zero a NI o, h0]) (by
      intro j hj
      have hl := j.isLt
      have hv : (sl1 a NI o j).val = f1 NI o j.val := vmap_val hb j
      unfold f1 at hv
      unfold need at hI hNI
      split_ifs at hv
      · exact absurd ‹_› hj
      · exact hI _ (by omega) (by omega)
      · exact hL _ (by omega) (by omega)
      · exact hI _ (by omega) (by omega))
  refine ⟨B, hs, b0, fun k => ?_, bj 23 (by omega)⟩
  fin_cases k <;> exact bj _ (by omega)

end Stages2

theorem sl3_zero (a : DecompositionAlgorithm) (NI o : ℕ) : sl3 a NI o ⟨0, by omega⟩ = pubPort NI 0 :=
  Fin.ext (by show (f3 NI o _ 0 % (2 + rowsWork NI)) = 0; simp [f3])

/-- The table stage under the all-heads masked reset. -/
theorem table_masked (s : ℕ) : ∃ B : Fin (RowsInit.LoopTable.N + 1) → List Bool,
    Step (MaskedReset.machine RowsInit.LoopTable.machine (fun _ => true)) (2 * RowsInit.LoopTable.tableCost s + 2)
      (fun _ => 0) (Fin.addCases (RowsInit.LoopTable.tin s) (fun _ : Fin 1 => [])) (fun _ => 0) B ∧
    B ⟨3, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^(s/2)) ∧
    B ⟨4, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^((s+1)/2)) ∧
    B ⟨5, by decide⟩ = List.replicate (2^s) true ∧ B ⟨6, by decide⟩ = List.replicate (2*2^s+1) false ∧
    B ⟨7, by decide⟩ = List.replicate (2^s) false := by
  obtain ⟨H', A', h, a3, -, a4, -, a5, -, a6, -, a7, -⟩ := RowsInit.LoopTable.table_run s
  obtain ⟨k, -, m⟩ := mask_empty h (fun _ => true) (fun _ _ => rfl)
  refine ⟨Fin.addCases (m := RowsInit.LoopTable.N) (n := 1) (motive := fun _ => List Bool) A'
    (fun _ => List.replicate k false), (m.congr_in (zeros_addCases _ _) rfl).congr (zeros_masked H') rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (Fin.addCases_left (motive := fun _ => List Bool) (3 : Fin RowsInit.LoopTable.N)).trans a3
  · exact (Fin.addCases_left (motive := fun _ => List Bool) (4 : Fin RowsInit.LoopTable.N)).trans a4
  · exact (Fin.addCases_left (motive := fun _ => List Bool) (5 : Fin RowsInit.LoopTable.N)).trans a5
  · exact (Fin.addCases_left (motive := fun _ => List Bool) (6 : Fin RowsInit.LoopTable.N)).trans a6
  · exact (Fin.addCases_left (motive := fun _ => List Bool) (7 : Fin RowsInit.LoopTable.N)).trans a7

section Stages3
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

/-- **Stage 2** (the fanout). -/
theorem stF (data : Fin 23 → List Bool) (R : ℕ) (hD : ∀ j, (data j).length ≤ R) (A1 : Fin (2 + rowsWork NI) → List Bool)
    (hs : ∀ j : Fin 23, A1 (wp NI (2 + o + j.val)) = data j)
    (hd : A1 (wp NI (2 + NI + 326)) = List.replicate R true)
    (hb : ∀ x : Fin (2 + rowsWork NI), RF NI o x.val → ¬ (2 + o ≤ x.val ∧ x.val < 2 + o + 23) →
      x.val ≠ 2 + NI + 326 → A1 x = []) :
    Step (mF NI o) (2 * R + 4) (fun _ => 0) A1 (fun _ => 0)
      (install (slF NI o) A1 (ExtIncidence.NativeFanout.output fanSel data R)) := by
  refine run_dock (fan_run data R hD) (slF NI o) (injF a NI o hNI) (fun _ => 0) A1 (fun _ => rfl) (fun l => ?_)
  have hl := l.isLt
  have hr := rF a NI o hNI l
  have hv : (slF NI o l).val = fF NI o l.val := vmap_val (bF a NI o hNI) l
  unfold need at hNI
  by_cases h1 : l.val < 23
  · have e : l = src ⟨l.val, h1⟩ := Fin.ext (by simp [src])
    have e2 : slF NI o l = wp NI (2 + o + l.val) := by
      show wp NI (fF NI o l.val) = _
      unfold fF; rw [if_pos h1]
    have e3 : ExtIncidence.NativeFanout.input data R l = data ⟨l.val, h1⟩ :=
      (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_src data R _)
    rw [e2, e3]; exact hs ⟨l.val, h1⟩
  · by_cases h2 : l.val < 532
    · have e : l = dst ⟨l.val - 23, by omega⟩ := Fin.ext (by simp [dst]; omega)
      have e3 : ExtIncidence.NativeFanout.input data R l = [] :=
        (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_dst data R _)
      rw [e3]
      refine hb _ hr ?_ ?_ <;> rw [hv] <;> unfold fF <;> split_ifs <;> omega
    · by_cases h3 : l.val = 532
      · have e : l = drvT := Fin.ext (by simp [drvT]; omega)
        have e2 : slF NI o l = wp NI (2 + NI + 326) := by
          show wp NI (fF NI o l.val) = _
          unfold fF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h3]
        have e3 : ExtIncidence.NativeFanout.input data R l = List.replicate R true :=
          (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_drv data R)
        rw [e2, e3]; exact hd
      · have e : l = logT := Fin.ext (by simp [logT]; omega)
        have e3 : ExtIncidence.NativeFanout.input data R l = [] :=
          (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_log data R)
        rw [e3]
        refine hb _ hr ?_ ?_ <;> rw [hv] <;> unfold fF <;> split_ifs <;> omega

/-- **Stage 3** (`auxVec`, masked). -/
theorem st3 (r : Request) (A2 : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A2 (pubPort NI 0) = frame (Request.input a r))
    (hb : ∀ x : Fin (2 + rowsWork NI), R3 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val →
      x.val ≠ 0 → A2 x = []) :
    ∃ B : Fin (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1) → List Bool,
      Step (m3 a NI o) (2 * (RowsInit.LoopAux.auxVec a).cost r + 2) (fun _ => 0) A2 (fun _ => 0)
        (install (sl3 a NI o) A2 B) ∧
      B ⟨0, by omega⟩ = frame (Request.input a r) ∧
      B ⟨1, by omega⟩ = frame (SignedSortKey.binary ((RowsInit.LoopAux.sOf a r + 1) / 2) 0) ∧
      B ⟨2, by omega⟩ = frame (SignedSortKey.binary (RowsInit.LoopAux.sOf a r / 2) 0) ∧
      B ⟨3, by omega⟩ = List.replicate (loopCl r.q) false ∧
      B ⟨4, by omega⟩ = List.replicate (loopDl r.q) false ∧
      B ⟨5, by omega⟩ = CloseoutRowsGateSupport.gateMembers (PCJ9eff70d512234a4c_Fixed.Packets.live (r.family a))ᶜ ∧
      B ⟨6, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word r.q ∧
      B ⟨7, by omega⟩ = List.replicate (RowsInit.LoopAux.sOf a r / 2) true ∧
      B ⟨8, by omega⟩ = List.replicate ((RowsInit.LoopAux.sOf a r + 1) / 2) true ∧
      B ⟨9, by omega⟩ = List.replicate (RowsInit.LoopAux.sOf a r) true := by
  have hb3 := b3 a NI o hNI
  obtain ⟨B, hs, b0, bj⟩ := vec_dock (RowsInit.LoopAux.auxVec a) r (sl3 a NI o) (inj3 a NI o hNI) (fun _ => 0) A2
    (fun _ => rfl) (by rw [sl3_zero a NI o, h0]) (by
      intro j hj
      have hv : (sl3 a NI o j).val = f3 NI o _ j.val := vmap_val hb3 j
      refine hb _ (r3 a NI o hNI j) ?_
      rw [hv]; unfold f3; split_ifs <;> omega)
  exact ⟨B, hs, b0, bj 0 (by omega), bj 1 (by omega), bj 2 (by omega), bj 3 (by omega), bj 4 (by omega),
    bj 5 (by omega), bj 6 (by omega), bj 7 (by omega), bj 8 (by omega)⟩

/-- **Stage 4** (the table machine, masked). -/
theorem st4 (sv : ℕ) (A3 : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A3 (wp NI (2 + o + 277)) = List.replicate (sv / 2) true)
    (h1 : A3 (wp NI (2 + o + 278)) = List.replicate ((sv + 1) / 2) true)
    (h2 : A3 (wp NI (2 + o + 279)) = List.replicate sv true)
    (hb : ∀ x : Fin (2 + rowsWork NI), R4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val →
      ¬ (2 + o + 277 ≤ x.val ∧ x.val ≤ 2 + o + 279) → A3 x = []) :
    ∃ B : Fin (RowsInit.LoopTable.N + 1) → List Bool,
      Step (m4 a NI o) (2 * RowsInit.LoopTable.tableCost sv + 2) (fun _ => 0) A3 (fun _ => 0)
        (install (sl4 a NI o) A3 B) ∧
      B ⟨3, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^(sv/2)) ∧
      B ⟨4, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^((sv+1)/2)) ∧
      B ⟨5, by decide⟩ = List.replicate (2^sv) true ∧ B ⟨6, by decide⟩ = List.replicate (2*2^sv+1) false ∧
      B ⟨7, by decide⟩ = List.replicate (2^sv) false := by
  obtain ⟨B, h, c3, c4, c5, c6, c7⟩ := table_masked sv
  have hb4 := b4 a NI o hNI
  refine ⟨B, run_dock h (sl4 a NI o) (inj4 a NI o hNI) (fun _ => 0) A3 (fun _ => rfl) (fun l => ?_), c3, c4, c5, c6, c7⟩
  have hl := l.isLt
  have hv : (sl4 a NI o l).val = f4 NI o _ _ l.val := vmap_val hb4 l
  unfold RowsInit.LoopTable.N at hl
  by_cases hlo : l.val < 69
  · have e : l = Fin.castAdd 1 (⟨l.val, hlo⟩ : Fin RowsInit.LoopTable.N) := Fin.ext rfl
    have ev : Fin.addCases (m := RowsInit.LoopTable.N) (n := 1) (motive := fun _ => List Bool) (RowsInit.LoopTable.tin sv)
        (fun _ : Fin 1 => []) l = RowsInit.LoopTable.tin sv ⟨l.val, hlo⟩ := by
      have h' := congrArg (Fin.addCases (m := RowsInit.LoopTable.N) (n := 1) (motive := fun _ => List Bool)
        (RowsInit.LoopTable.tin sv) (fun _ : Fin 1 => [])) e
      rw [h', Fin.addCases_left]
    rw [ev]
    have ew : ∀ v, l.val = v → sl4 a NI o l = wp NI (f4 NI o (RowsInit.LoopWords.loopVec a).extra
        (RowsInit.LoopAux.auxVec a).extra v) := by intro v hv'; show wp NI _ = _; rw [hv']
    by_cases l0 : l.val = 0
    · rw [ew 0 l0, show f4 NI o _ _ 0 = 2 + o + 277 by simp [f4], h0]; simp [RowsInit.LoopTable.tin, l0]
    by_cases l1 : l.val = 1
    · rw [ew 1 l1, show f4 NI o _ _ 1 = 2 + o + 278 by simp [f4], h1]; simp [RowsInit.LoopTable.tin, l1]
    by_cases l2 : l.val = 2
    · rw [ew 2 l2, show f4 NI o _ _ 2 = 2 + o + 279 by simp [f4], h2]; simp [RowsInit.LoopTable.tin, l2]
    have et : RowsInit.LoopTable.tin sv ⟨l.val, hlo⟩ = [] := by
      simp only [RowsInit.LoopTable.tin]; rw [if_neg l0, if_neg l1, if_neg l2]
    rw [et]
    refine hb _ (r4 a NI o hNI l) ?_
    rw [hv]; unfold f4; split_ifs <;> omega
  · have e : l = Fin.natAdd RowsInit.LoopTable.N (0 : Fin 1) :=
      Fin.ext (by show l.val = RowsInit.LoopTable.N + 0; unfold RowsInit.LoopTable.N; omega)
    have ev : Fin.addCases (m := RowsInit.LoopTable.N) (n := 1) (motive := fun _ => List Bool) (RowsInit.LoopTable.tin sv)
        (fun _ : Fin 1 => []) l = [] := by rw [e, Fin.addCases_right]
    rw [ev]
    refine hb _ (r4 a NI o hNI l) ?_
    rw [hv]; unfold f4; split_ifs <;> omega

end Stages3

/-! ## 6. The consumer's loop bank, port by port -/

theorem lb_lt {q : ℕ} (live : Finset (Fin q)) (R : ℕ) (M : Fin 254 → List Bool) (v : ℕ) (hv : v < MT+1+1)
    (h : v < MT) :
    loopBank live R M ⟨v, hv⟩ = tapes live liveᶜ.card R (loopCl q) (loopDl q) 0 0 M
      (List.replicate (2^liveᶜ.card) false) ⟨v, h⟩ := by
  have e : (⟨v, hv⟩ : Fin (MT+1+1)) = Fin.castAdd 1 (Fin.castAdd 1 (⟨v, h⟩ : Fin MT)) := Fin.ext rfl
  rw [e]; unfold loopBank; rw [Fin.addCases_left, Fin.addCases_left]

theorem lb_c0 {q : ℕ} (live : Finset (Fin q)) (R : ℕ) (M : Fin 254 → List Bool) (i : Fin (MT+1+1)) (h : i.val = MT) :
    loopBank live R M i = RepairSource.VerifierDecoding.CompareMachine.word (2^(liveᶜ.card/2)) := by
  have e : i = Fin.castAdd 1 (Fin.natAdd MT (0 : Fin 1)) := Fin.ext (by simp [h])
  rw [e]; unfold loopBank; rw [Fin.addCases_left, Fin.addCases_right]

theorem lb_c1 {q : ℕ} (live : Finset (Fin q)) (R : ℕ) (M : Fin 254 → List Bool) (i : Fin (MT+1+1)) (h : i.val = MT + 1) :
    loopBank live R M i = RepairSource.VerifierDecoding.CompareMachine.word (2^((liveᶜ.card+1)/2)) := by
  have e : i = Fin.natAdd (MT+1) (0 : Fin 1) := Fin.ext (by simp [h])
  rw [e]; unfold loopBank; rw [Fin.addCases_right]

theorem tp_cell {q : ℕ} (live : Finset (Fin q)) (s R C D rowN colN : ℕ) (M : Fin 254 → List Bool) (out : List Bool)
    (v : ℕ) (h : v < MT) (hv : v < 257) :
    tapes live s R C D rowN colN M out ⟨v, h⟩ =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out ⟨v, hv⟩ := by
  have e : (⟨v, h⟩ : Fin MT) = cellP ⟨v, hv⟩ := Fin.ext rfl
  rw [e]; unfold tapes; rw [layout_cell]

theorem tp_master {q : ℕ} (live : Finset (Fin q)) (s R C D rowN colN : ℕ) (M : Fin 254 → List Bool) (out : List Bool)
    (v : ℕ) (h : v < MT) (h1 : 257 ≤ v) (h2 : v < 511) :
    tapes live s R C D rowN colN M out ⟨v, h⟩ = M ⟨v - 257, by omega⟩ := by
  have e : (⟨v, h⟩ : Fin MT) = masterP ⟨v - 257, by omega⟩ := Fin.ext (by simp [masterP_val]; omega)
  rw [e]; unfold tapes; rw [layout_master]

theorem tp_aux {q : ℕ} (live : Finset (Fin q)) (s R C D rowN colN : ℕ) (M : Fin 254 → List Bool) (out : List Bool)
    (v : ℕ) (h : v < MT) (h1 : 511 ≤ v) :
    tapes live s R C D rowN colN M out ⟨v, h⟩ = aux live s C D rowN colN (List.replicate R false) ⟨v - 511, by
      simp [MT] at h; omega⟩ := by
  have e : (⟨v, h⟩ : Fin MT) = auxP ⟨v - 511, by simp [MT] at h; omega⟩ := Fin.ext (by simp [auxP_val]; omega)
  rw [e]; unfold tapes; rw [layout_aux]

theorem vf_lt (A : Fin 254 → List Bool) (R : ℕ) (out : List Bool) (v : ℕ) (hv : v < 257) (h : v < 254) :
    PCJ45bee56da9f34d5a_VerdictFinish.bank A R out ⟨v, hv⟩ = A ⟨v, h⟩ := by
  have e : (⟨v, hv⟩ : Fin 257) = Fin.castAdd 3 (⟨v, h⟩ : Fin 254) := Fin.ext rfl
  rw [e]; unfold PCJ45bee56da9f34d5a_VerdictFinish.bank; rw [Fin.addCases_left]

theorem vf_hi (A : Fin 254 → List Bool) (R : ℕ) (out : List Bool) (v : ℕ) (hv : v < 257) (h : 254 ≤ v) :
    PCJ45bee56da9f34d5a_VerdictFinish.bank A R out ⟨v, hv⟩ =
      (![List.replicate R true, List.replicate (R+1) false, out] : Fin 3 → List Bool) ⟨v - 254, by omega⟩ := by
  have e : (⟨v, hv⟩ : Fin 257) = Fin.natAdd 254 (⟨v - 254, by omega⟩ : Fin 3) := Fin.ext (by simp; omega)
  rw [e]; unfold PCJ45bee56da9f34d5a_VerdictFinish.bank; rw [Fin.addCases_right]

/-! ## 7. The source words fit the capacity (`thr_hml` at witnessing ports) -/

def wit : Fin 23 → Fin 254 :=
  ![2, 3, 4, 5, 6, 7, 105, 108, 112, 124, 137, 147, 152, 156, 190, 216, 234, 235, 236, 223, 237, 227, 232]

theorem wit_sel : ∀ j, thrSel (wit j) = some j := by decide
theorem wit_key : ∀ j, wit j ∉ keyPorts := by decide

theorem src_len (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k0 : RCFive.RowKeys.ThrKey a r L target) (j : Fin 23) :
    (srcOf a (.thr r four L target) j).length ≤ thrRes r.q (ThrWidth.T a r four L target) := by
  have h1 := master_fan a r four L target k0 (wit j) (Or.inl (wit_key j))
  have h2 := thr_hml a r four L target (thrRes r.q (ThrWidth.T a r four L target)) (thrR_le_res _ _) k0 (wit j)
  rw [h1, wit_sel j] at h2
  simp only [Option.elim, ZeroPadding.pad_length] at h2
  omega

theorem keyPorts_iff : ∀ k : Fin 254, k ∈ keyPorts ↔ (k.val = 109 ∨ isKey k.val) := by decide

theorem dst_val (v : ℕ) (h : v < 509) : (dst ⟨v, h⟩).val = 23 + v := by simp [dst]

/-! ## 8. The chained banks, port by port -/

section Banks
variable (a : DecompositionAlgorithm) (NI o : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
  (B1 : Fin (1 + 24 + (RowsInit.LoopWords.loopVec a).extra + 1) → List Bool) (data : Fin 23 → List Bool) (R : ℕ)
  (B3 : Fin (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1) → List Bool) (B4 : Fin (RowsInit.LoopTable.N + 1) → List Bool)

def bk1 := install (sl1 a NI o) A B1
def bk2 := install (slF NI o) (bk1 a NI o A B1) (ExtIncidence.NativeFanout.output fanSel data R)
def bk3 := install (sl3 a NI o) (bk2 a NI o A B1 data R) B3
def bk4 := install (sl4 a NI o) (bk3 a NI o A B1 data R B3) B4

variable (hNI : o + need a ≤ NI)
include hNI

theorem bk1_out (x : Fin (2 + rowsWork NI)) (h1 : ¬ R1 NI o (RowsInit.LoopWords.loopVec a).extra x.val) :
    bk1 a NI o A B1 x = A x := inst_out _ _ _ x _ (r1 a NI o hNI) h1
theorem bk2_out (x : Fin (2 + rowsWork NI)) (hF : ¬ RF NI o x.val) :
    bk2 a NI o A B1 data R x = bk1 a NI o A B1 x := inst_out _ _ _ x _ (rF a NI o hNI) hF
theorem bk3_out (x : Fin (2 + rowsWork NI))
    (h3 : ¬ R3 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk3 a NI o A B1 data R B3 x = bk2 a NI o A B1 data R x := inst_out _ _ _ x _ (r3 a NI o hNI) h3
theorem bk4_out (x : Fin (2 + rowsWork NI))
    (h4 : ¬ R4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = bk3 a NI o A B1 data R B3 x := inst_out _ _ _ x _ (r4 a NI o hNI) h4

theorem bk4_F (x : Fin (2 + rowsWork NI)) (l : Fin (23 + (509 + 1) + 1)) (hx : x.val = fF NI o l.val)
    (h4 : ¬ R4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (h3 : ¬ R3 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = ExtIncidence.NativeFanout.output fanSel data R l := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4, bk3_out a NI o A B1 data R B3 hNI x h3,
    show x = slF NI o l from Fin.ext (hx.trans (vmap_val (bF a NI o hNI) l).symm)]
  exact install_slot _ (injF a NI o hNI) _ _ _

theorem bk4_3 (x : Fin (2 + rowsWork NI)) (l : Fin (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1))
    (hx : x.val = f3 NI o (RowsInit.LoopWords.loopVec a).extra l.val)
    (h4 : ¬ R4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = B3 l := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4, show x = sl3 a NI o l from Fin.ext (hx.trans (vmap_val (b3 a NI o hNI) l).symm)]
  exact install_slot _ (inj3 a NI o hNI) _ _ _

theorem bk4_4 (x : Fin (2 + rowsWork NI)) (l : Fin (RowsInit.LoopTable.N + 1))
    (hx : x.val = f4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra l.val) :
    bk4 a NI o A B1 data R B3 B4 x = B4 l := by
  rw [show x = sl4 a NI o l from Fin.ext (hx.trans (vmap_val (b4 a NI o hNI) l).symm)]
  exact install_slot _ (inj4 a NI o hNI) _ _ _

theorem bk_all (x : Fin (2 + rowsWork NI))
    (h4 : ¬ R4 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (h3 : ¬ R3 NI o (RowsInit.LoopWords.loopVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (hF : ¬ RF NI o x.val) (h1 : ¬ R1 NI o (RowsInit.LoopWords.loopVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = A x := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4, bk3_out a NI o A B1 data R B3 hNI x h3,
    bk2_out a NI o A B1 data R hNI x hF, bk1_out a NI o A B1 hNI x h1]

end Banks

/-! ## 9. The run -/

section Run
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem chain (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k0 : RCFive.RowKeys.ThrKey a r L target) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.thr r four L target)))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ B1 B3 B4, Step (machine a NI o) (cost a (.thr r four L target)) (fun _ => 0) A (fun _ => 0)
        (bk4 a NI o A B1 (srcOf a (.thr r four L target)) (thrRes r.q (ThrWidth.T a r four L target)) B3 B4) ∧
      B3 ⟨0, by omega⟩ = frame (Request.input a (.thr r four L target)) ∧
      B3 ⟨1, by omega⟩ = frame (SignedSortKey.binary ((RowsInit.LoopAux.sOf a (.thr r four L target) + 1) / 2) 0) ∧
      B3 ⟨2, by omega⟩ = frame (SignedSortKey.binary (RowsInit.LoopAux.sOf a (.thr r four L target) / 2) 0) ∧
      B3 ⟨3, by omega⟩ = List.replicate (loopCl r.q) false ∧
      B3 ⟨4, by omega⟩ = List.replicate (loopDl r.q) false ∧
      B3 ⟨5, by omega⟩ = CloseoutRowsGateSupport.gateMembers
        (PCJ9eff70d512234a4c_Fixed.Packets.live ((Request.thr r four L target).family a))ᶜ ∧
      B3 ⟨6, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word r.q ∧
      B4 ⟨3, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^(RowsInit.LoopAux.sOf a (.thr r four L target)/2)) ∧
      B4 ⟨4, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word
        (2^((RowsInit.LoopAux.sOf a (.thr r four L target)+1)/2)) ∧
      B4 ⟨5, by decide⟩ = List.replicate (2^RowsInit.LoopAux.sOf a (.thr r four L target)) true ∧
      B4 ⟨6, by decide⟩ = List.replicate (2*2^RowsInit.LoopAux.sOf a (.thr r four L target)+1) false ∧
      B4 ⟨7, by decide⟩ = List.replicate (2^RowsInit.LoopAux.sOf a (.thr r four L target)) false := by
  have hn := hNI
  unfold need at hn
  have i1 := inj1 a NI o hNI
  have i3 := inj3 a NI o hNI
  obtain ⟨B1, s1, b10, b1s, b1c⟩ := st1 a NI o hNI (.thr r four L target) A h0 hI hL
  have s2 := stF a NI o hNI (srcOf a (.thr r four L target)) (thrRes r.q (ThrWidth.T a r four L target))
    (src_len a r four L target k0) (bk1 a NI o A B1)
    (fun j => by unfold bk1; rw [← sl1_src a NI o j, install_slot _ i1]; exact b1s j)
    (by unfold bk1; rw [← sl1_clock a NI o, install_slot _ i1]; exact b1c) (by
      intro x hx hns hnc
      unfold RF isKey at hx
      rw [bk1_out a NI o A B1 hNI x (by unfold R1; omega)]
      rcases hx with h | h | h | h
      · exact hI x (by omega) (by unfold need; omega)
      · exact hL x (by omega) (by omega)
      · exact hL x (by omega) (by omega)
      · exact hL x (by omega) (by omega))
  obtain ⟨B3, s3, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39⟩ := st3 a NI o hNI (.thr r four L target)
    (bk2 a NI o A B1 (srcOf a (.thr r four L target)) (thrRes r.q (ThrWidth.T a r four L target))) (by
      rw [bk2_out a NI o A B1 _ _ hNI _ (by show ¬ RF NI o 0; unfold RF; omega)]
      unfold bk1; rw [← sl1_zero a NI o, install_slot _ i1]; exact b10) (by
      intro x hx hx0
      unfold R3 at hx
      rw [bk2_out a NI o A B1 _ _ hNI x (by unfold RF isKey; omega), bk1_out a NI o A B1 hNI x (by unfold R1; omega)]
      rcases hx with h | h | h | h
      · exact absurd h hx0
      · exact hL x (by omega) (by omega)
      · exact hI x (by omega) (by unfold need; omega)
      · exact hI x (by omega) (by unfold need; omega))
  have e3 : ∀ m : ℕ, (h1 : 7 ≤ m) → (h2 : m ≤ 9) → wp NI (2 + o + 270 + m) = sl3 a NI o ⟨m, by omega⟩ := by
    intro m h1 h2; show _ = wp NI (f3 NI o _ m); congr 1; unfold f3; split_ifs <;> omega
  obtain ⟨B4, s4, c3, c4, c5, c6, c7⟩ := st4 a NI o hNI (RowsInit.LoopAux.sOf a (.thr r four L target))
    (bk3 a NI o A B1 (srcOf a (.thr r four L target)) (thrRes r.q (ThrWidth.T a r four L target)) B3)
    (by unfold bk3; rw [show 2 + o + 277 = 2 + o + 270 + 7 by omega, e3 7 (by omega) (by omega), install_slot _ i3]; exact b37)
    (by unfold bk3; rw [show 2 + o + 278 = 2 + o + 270 + 8 by omega, e3 8 (by omega) (by omega), install_slot _ i3]; exact b38)
    (by unfold bk3; rw [show 2 + o + 279 = 2 + o + 270 + 9 by omega, e3 9 (by omega) (by omega), install_slot _ i3]; exact b39)
    (by
      intro x hx hnt
      unfold R4 at hx
      rw [bk3_out a NI o A B1 _ _ B3 hNI x (by unfold R3; omega), bk2_out a NI o A B1 _ _ hNI x (by unfold RF isKey; omega),
        bk1_out a NI o A B1 hNI x (by unfold R1; omega)]
      rcases hx with h | h | h | h
      · exact absurd h hnt
      · exact hL x (by omega) (by omega)
      · exact hL x (by omega) (by omega)
      · exact hI x (by omega) (by unfold need; omega))
  exact ⟨B1, B3, B4, ((s1.seq s2).seq s3).seq s4, b30, b31, b32, b33, b34, b35, b36, c3, c4, c5, c6, c7⟩

/-- **The THR loop block and C6 words of `thrBase 0`** (the ten key masters left blank, the entry form of RC5's key-0
writer), from a work bank whose request port holds the framed request and whose loop/C6 blocks and init region
`[o, o + need a)` are blank; every other port is untouched. `k₀` is any key (the non-key masters do not depend on it). -/
theorem loop_run (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k0 : RCFive.RowKeys.ThrKey a r L target) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.thr r four L target)))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a NI o) (cost a (.thr r four L target)) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k ∈ thrKeySet, A' (masterPort NI k) = []) ∧
      (∀ i : Fin (MT+1+1), (∀ k ∈ thrKeySet, loopPort NI i ≠ masterPort NI k) →
        A' (loopPort NI i) = loopBank (thrLive r L) (thrRes r.q (ThrWidth.T a r four L target))
          (thrMasters a r four L target (thrRes r.q (ThrWidth.T a r four L target)) k0) i) ∧
      (∀ i, A' (c6Port NI i) = c6Words (thrLive r L)ᶜ.card i) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 + o ≤ x.val ∧ x.val < 2 + o + need a) →
        ¬ (2 + NI + 72 ≤ x.val ∧ x.val < 2 + NI + 594) → A' x = A x) := by
  have hn := hNI
  unfold need at hn
  have hneed : need a = 344 + (RowsInit.LoopWords.loopVec a).extra + (RowsInit.LoopAux.auxVec a).extra := rfl
  obtain ⟨B1, B3, B4, hs, b30, b31, b32, b33, b34, b35, b36, c3, c4, c5, c6, c7⟩ :=
    chain a NI o hNI r four L target k0 A h0 hI hL
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkv := master_val NI k
    have hkey := (isKey_iff k).2 hk
    have hk' := k.isLt
    rw [bk_all a NI o A B1 _ _ B3 B4 hNI _ (by unfold R4; omega) (by unfold R3; omega) (by
        unfold RF; intro h
        rcases h with h | h | ⟨-, -, h⟩ | h
        · omega
        · omega
        · exact h (by rw [show (masterPort NI k).val - (2 + NI + 329) = k.val by omega]; exact hkey)
        · omega) (by unfold R1; omega)]
    exact hL _ (by omega) (by omega)
  · intro i hi
    obtain ⟨v, hv⟩ := i
    have hvx : (loopPort NI ⟨v, hv⟩).val = 2 + NI + 72 + v := loop_val NI ⟨v, hv⟩
    have hv' : v < 520 := by simpa [MT] using hv
    by_cases hc : v < 257
    · rw [lb_lt _ _ _ v hv (by simp [MT]; omega), tp_cell _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) hc]
      by_cases hc1 : v < 254
      · rw [vf_lt _ _ _ v hc hc1, bk4_F a NI o A B1 _ _ B3 B4 hNI _ (dst ⟨v, by omega⟩)
          (by rw [hvx, dst_val]; unfold fF; split_ifs <;> omega) (by unfold R4; omega) (by unfold R3; omega),
          out_blank _ _ _ (Or.inl hc1)]
      · rw [vf_hi _ _ _ v hc (by omega)]
        by_cases h254 : v = 254
        · subst h254
          rw [bk4_F a NI o A B1 _ _ B3 B4 hNI _ drvT (by rw [hvx]; simp [drvT, fF]) (by unfold R4; omega)
            (by unfold R3; omega), out_drv]; rfl
        by_cases h255 : v = 255
        · subst h255
          rw [bk4_F a NI o A B1 _ _ B3 B4 hNI _ logT (by rw [hvx]; simp [logT, fF]) (by unfold R4; omega)
            (by unfold R3; omega), out_log]; rfl
        have h256 : v = 256 := by omega
        subst h256
        rw [bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨7, by decide⟩ (by rw [hvx]; simp [f4]), c7]; rfl
    by_cases hm : v < 511
    · rw [lb_lt _ _ _ v hv (by simp [MT]; omega), tp_master _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) (by omega) hm]
      have hnk : ¬ isKey (v - 257) := by
        intro hk
        have hkk : (⟨v - 257, by omega⟩ : Fin 254) ∈ thrKeySet := (isKey_iff _).1 hk
        exact hi _ hkk (Fin.ext (by rw [hvx, master_val]; simp; omega))
      rw [bk4_F a NI o A B1 _ _ B3 B4 hNI _ (dst ⟨254 + (v - 257), by omega⟩) (by
          rw [hvx, dst_val]; unfold fF; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          rw [if_neg (by rw [show 23 + (254 + (v - 257)) - 277 = v - 257 by omega]; exact hnk)]; omega)
        (by unfold R4; omega) (by unfold R3; omega)]
      rw [out_master _ _ ⟨v - 257, by omega⟩]
      by_cases h109 : v - 257 = 109
      · rw [master_fan a r four L target k0 _ (Or.inr (Fin.ext h109))]
      · rw [master_fan a r four L target k0 _ (Or.inl (by
          rw [keyPorts_iff]; intro h; rcases h with h | h
          · exact h109 h
          · exact hnk h))]
    by_cases ha : v < 518
    · rw [lb_lt _ _ _ v hv (by simp [MT]; omega), tp_aux _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) (by omega)]
      by_cases a0 : v = 511
      · subst a0; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨1, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b31]; rfl
      by_cases a1 : v = 512
      · subst a1; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨2, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b32]; rfl
      by_cases a2 : v = 513
      · subst a2
        rw [bk4_F a NI o A B1 _ _ B3 B4 hNI _ (dst ⟨508, by omega⟩) (by rw [hvx, dst_val]; simp [fF])
          (by unfold R4; omega) (by unfold R3; omega), out_blank _ _ _ (Or.inr rfl)]; rfl
      by_cases a3 : v = 514
      · subst a3; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨3, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b33]; rfl
      by_cases a4 : v = 515
      · subst a4; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨4, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b34]; rfl
      by_cases a5 : v = 516
      · subst a5; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨5, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b35]; rfl
      have a6 : v = 517 := by omega
      subst a6; rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI _ ⟨6, by omega⟩ (by rw [hvx]; simp [f3]) (by unfold R4; omega), b36]; rfl
    by_cases h518 : v = 518
    · subst h518
      rw [lb_c0 _ _ _ _ (by simp [MT]), bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨3, by decide⟩ (by rw [hvx]; simp [f4]), c3]; rfl
    have h519 : v = 519 := by omega
    subst h519
    rw [lb_c1 _ _ _ _ (by simp [MT]), bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨4, by decide⟩ (by rw [hvx]; simp [f4]), c4]; rfl
  · intro i
    fin_cases i
    · rw [bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨5, by decide⟩ (by rw [c6_val]; simp [f4]), c5]; rfl
    · rw [bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨6, by decide⟩ (by rw [c6_val]; simp [f4]), c6]; rfl
  · intro x hxI hxL
    by_cases hx0 : x.val = 0
    · rw [bk4_3 a NI o A B1 _ _ B3 B4 hNI x ⟨0, by omega⟩ (by rw [hx0]; simp [f3]) (by unfold R4; omega), b30,
        show x = pubPort NI 0 from Fin.ext hx0, h0]
    · exact bk_all a NI o A B1 _ _ B3 B4 hNI x (by unfold R4; omega) (by unfold R3; omega) (by unfold RF isKey; omega)
        (by unfold R1; omega)

end Run

end
end RowsInit.ThrLoop
