import Proof.Rows.RowsSymLoopWords
import Proof.Rows.RowsInitThrLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.SymLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.VecDock RowsInit.SymLoopFan PCJd4d1d9d7d1fa4313_Production
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj inst_out rw_eq pub_val loop_val c6_val master_val)
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
noncomputable section

/-! ## 1. The four SYM key masters -/

/-- The four SYM key masters (140–143), as a predicate on the master index. -/
def isKey (k : ℕ) : Prop := 140 ≤ k ∧ k ≤ 143

instance (k : ℕ) : Decidable (isKey k) := by unfold isKey; infer_instance

theorem isKey_iff (k : Fin 254) : isKey k.val ↔ k ∈ symKeySet := by
  unfold isKey symKeySet
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  constructor
  · intro h
    have : k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 := by omega
    simpa using this
  · intro h
    simp at h
    omega

/-! ## 2. The four slot maps (init region `[o, o + need a)`) -/

/-- The init ports the block uses: sources 17, key junk 4, table inputs 3, and the three stages' scratch. -/
def need (a : DecompositionAlgorithm) : ℕ :=
  88 + (RowsInit.SymLoopWords.symVec a).extra + (RowsInit.LoopAux.auxVec a).extra

/-- `symVec`: request (pub 0), sources (init `o..o+16`), clock (loop cell 254), scratch (init `o+24..`). -/
def f1 (NI o v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 17 then 2 + o + (v - 1) else if v = 18 then 2 + NI + 326 else 2 + o + 24 + (v - 19)

/-- The fanout: sources, 254 cells, 254 masters (key ones to junk init `o+17..o+20`), aux 2, clock, log. -/
def fF (NI o v : ℕ) : ℕ :=
  if v < 17 then 2 + o + v else if v < 271 then 2 + NI + 72 + (v - 17)
  else if v < 525 then (if isKey (v - 271) then 2 + o + 17 + (v - 411) else 2 + NI + 329 + (v - 271))
  else if v = 525 then 2 + NI + 585 else if v = 526 then 2 + NI + 326 else 2 + NI + 327

/-- `auxVec`: request, aux 0,1,3,4,5,6, table inputs (init `o+21..o+23`), scratch (init `o+25+eV..`). -/
def f3 (NI o eV v : ℕ) : ℕ :=
  if v = 0 then 0 else if v ≤ 2 then 2 + NI + 582 + v else if v ≤ 6 then 2 + NI + 583 + v
  else if v ≤ 9 then 2 + o + 14 + v else 2 + o + 15 + eV + v

/-- The table stage: inputs, counters (loop 518, 519), C6, verdict (cell 256), scratch (init `o+26+eV+eA..`). -/
def f4 (NI o eV eA v : ℕ) : ℕ :=
  if v ≤ 2 then 2 + o + 21 + v else if v = 3 then 2 + NI + 590 else if v = 4 then 2 + NI + 591
  else if v = 5 then 2 + NI + 592 else if v = 6 then 2 + NI + 593 else if v = 7 then 2 + NI + 328
  else 2 + o + 18 + eV + eA + v

def sl1 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  vmap NI (1 + 18 + (RowsInit.SymLoopWords.symVec a).extra + 1) (f1 NI o)
def slF (NI o : ℕ) := vmap NI (17 + (509 + 1) + 1) (fF NI o)
def sl3 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  vmap NI (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1) (f3 NI o ((RowsInit.SymLoopWords.symVec a).extra))
def sl4 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  vmap NI (RowsInit.LoopTable.N + 1)
    (f4 NI o ((RowsInit.SymLoopWords.symVec a).extra) ((RowsInit.LoopAux.auxVec a).extra))

section Maps
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem b1 : ∀ v, v < 1 + 18 + (RowsInit.SymLoopWords.symVec a).extra + 1 → f1 NI o v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f1; split_ifs <;> omega
theorem bF : ∀ v, v < 17 + (509 + 1) + 1 → fF NI o v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold fF; split_ifs <;> omega
theorem b3 : ∀ v, v < 1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1 →
    f3 NI o ((RowsInit.SymLoopWords.symVec a).extra) v < 2 + rowsWork NI := by
  intro v hv; unfold need at hNI; rw [rw_eq]; unfold f3; split_ifs <;> omega
theorem b4 : ∀ v, v < RowsInit.LoopTable.N + 1 →
    f4 NI o ((RowsInit.SymLoopWords.symVec a).extra) ((RowsInit.LoopAux.auxVec a).extra) v < 2 + rowsWork NI := by
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

def R1 (NI o eV v : ℕ) : Prop :=
  v = 0 ∨ (2 + o ≤ v ∧ v < 2 + o + 17) ∨ v = 2 + NI + 326 ∨ (2 + o + 24 ≤ v ∧ v ≤ 2 + o + 24 + eV)
def RF (NI o v : ℕ) : Prop :=
  (2 + o ≤ v ∧ v < 2 + o + 21) ∨ (2 + NI + 72 ≤ v ∧ v < 2 + NI + 328) ∨
  (2 + NI + 329 ≤ v ∧ v < 2 + NI + 583 ∧ ¬ isKey (v - (2 + NI + 329))) ∨ v = 2 + NI + 585
def R3 (NI o eV eA v : ℕ) : Prop :=
  v = 0 ∨ (2 + NI + 583 ≤ v ∧ v ≤ 2 + NI + 589 ∧ v ≠ 2 + NI + 585) ∨ (2 + o + 21 ≤ v ∧ v ≤ 2 + o + 23) ∨
  (2 + o + 25 + eV ≤ v ∧ v ≤ 2 + o + 25 + eV + eA)
def R4 (NI o eV eA v : ℕ) : Prop :=
  (2 + o + 21 ≤ v ∧ v ≤ 2 + o + 23) ∨ (2 + NI + 590 ≤ v ∧ v ≤ 2 + NI + 593) ∨ v = 2 + NI + 328 ∨
  (2 + o + 26 + eV + eA ≤ v ∧ v ≤ 2 + o + 87 + eV + eA)

section Ranges
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem r1 : ∀ j, R1 NI o ((RowsInit.SymLoopWords.symVec a).extra) (sl1 a NI o j).val := by
  intro j; have := j.isLt; unfold sl1; rw [vmap_val (b1 a NI o hNI)]; unfold R1 f1; split_ifs <;> omega
theorem rF : ∀ j, RF NI o (slF NI o j).val := by
  intro j; have := j.isLt; unfold slF; rw [vmap_val (bF a NI o hNI)]; unfold RF fF
  split_ifs with h1 h2 h3 h4 <;> first | omega | (unfold isKey at *; omega) |
    (right; right; left; refine ⟨by omega, by omega, ?_⟩;
      rwa [show 2 + NI + 329 + (j.val - 271) - (2 + NI + 329) = j.val - 271 by omega])
theorem r3 : ∀ j, R3 NI o ((RowsInit.SymLoopWords.symVec a).extra) ((RowsInit.LoopAux.auxVec a).extra)
    (sl3 a NI o j).val := by
  intro j; have := j.isLt; unfold sl3; rw [vmap_val (b3 a NI o hNI)]; unfold R3 f3; split_ifs <;> omega
theorem r4 : ∀ j, R4 NI o ((RowsInit.SymLoopWords.symVec a).extra) ((RowsInit.LoopAux.auxVec a).extra)
    (sl4 a NI o j).val := by
  intro j; have := j.isLt; unfold sl4; rw [vmap_val (b4 a NI o hNI)]; unfold R4 f4 RowsInit.LoopTable.N at *
  split_ifs <;> omega

end Ranges

/-! ## 4. The machine and its cost -/

def m1 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl1 a NI o) (MaskedReset.machine (RowsInit.SymLoopWords.symVec a).machine (fun _ => true))
def mF (NI o : ℕ) := RecoveryFocus.machine (slF NI o) (ExtIncidence.NativeFanout.machine fanSel)
def m3 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl3 a NI o) (MaskedReset.machine (RowsInit.LoopAux.auxVec a).machine (fun _ => true))
def m4 (a : DecompositionAlgorithm) (NI o : ℕ) :=
  RecoveryFocus.machine (sl4 a NI o) (MaskedReset.machine RowsInit.LoopTable.machine (fun _ => true))

/-- **The SYM loop-block writer** (one fixed machine per `a`, `NI`, `o`). -/
def machine (a : DecompositionAlgorithm) (NI o : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (m1 a NI o) (mF NI o)) (m3 a NI o)) (m4 a NI o)

/-- Its cost at a request. -/
def cost (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (((2 * (RowsInit.SymLoopWords.symVec a).cost r + 2) + 1 + (2 * symRes r.q (r.input a).length + 4)) + 1 +
    (2 * (RowsInit.LoopAux.auxVec a).cost r + 2)) + 1 + (2 * RowsInit.LoopTable.tableCost (RowsInit.complCount a r) + 2)

/-! ## 5. The four stages -/

theorem sl1_zero (a : DecompositionAlgorithm) (NI o : ℕ) : sl1 a NI o ⟨0, by omega⟩ = pubPort NI 0 :=
  Fin.ext (by show (0 % (2 + rowsWork NI)) = 0; exact Nat.zero_mod _)

theorem sl1_src (a : DecompositionAlgorithm) (NI o : ℕ) (j : Fin 17) :
    sl1 a NI o ⟨j.val + 1, by omega⟩ = wp NI (2 + o + j.val) := by
  show wp NI (f1 NI o (j.val + 1)) = _
  have hj := j.isLt
  have e : f1 NI o (j.val + 1) = 2 + o + j.val := by
    unfold f1
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  rw [e]

theorem sl1_clock (a : DecompositionAlgorithm) (NI o : ℕ) : sl1 a NI o ⟨18, by omega⟩ = wp NI (2 + NI + 326) := by
  show wp NI (f1 NI o 18) = _
  congr 1

section Stages
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

/-- **Stage 1** (`symVec`, masked): sources on init `o..o+16`, clock `1^R` on loop cell 254. -/
theorem st1 (r : Request) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a r))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ B : Fin (1 + 18 + (RowsInit.SymLoopWords.symVec a).extra + 1) → List Bool,
      Step (m1 a NI o) (2 * (RowsInit.SymLoopWords.symVec a).cost r + 2) (fun _ => 0) A (fun _ => 0)
        (install (sl1 a NI o) A B) ∧
      B ⟨0, by omega⟩ = frame (Request.input a r) ∧
      (∀ j : Fin 17, B ⟨j.val + 1, by omega⟩ = symSrcOf a r j) ∧
      B ⟨18, by omega⟩ = List.replicate (symRes r.q (r.input a).length) true := by
  have hb := b1 a NI o hNI
  obtain ⟨B, hs, b0, bj⟩ := vec_dock (RowsInit.SymLoopWords.symVec a) r (sl1 a NI o) (inj1 a NI o hNI) (fun _ => 0) A
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
  refine ⟨B, hs, b0, fun k => ?_, bj 17 (by omega)⟩
  fin_cases k <;> exact bj _ (by omega)

end Stages

theorem sl3_zero (a : DecompositionAlgorithm) (NI o : ℕ) : sl3 a NI o ⟨0, by omega⟩ = pubPort NI 0 :=
  Fin.ext (by show (f3 NI o _ 0 % (2 + rowsWork NI)) = 0; simp [f3])

section Stages3
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

/-- **Stage 2** (the fanout). -/
theorem stF (data : Fin 17 → List Bool) (R : ℕ) (hD : ∀ j, (data j).length ≤ R) (A1 : Fin (2 + rowsWork NI) → List Bool)
    (hs : ∀ j : Fin 17, A1 (wp NI (2 + o + j.val)) = data j)
    (hd : A1 (wp NI (2 + NI + 326)) = List.replicate R true)
    (hb : ∀ x : Fin (2 + rowsWork NI), RF NI o x.val → ¬ (2 + o ≤ x.val ∧ x.val < 2 + o + 17) →
      x.val ≠ 2 + NI + 326 → A1 x = []) :
    Step (mF NI o) (2 * R + 4) (fun _ => 0) A1 (fun _ => 0)
      (install (slF NI o) A1 (ExtIncidence.NativeFanout.output fanSel data R)) := by
  refine run_dock (fan_run data R hD) (slF NI o) (injF a NI o hNI) (fun _ => 0) A1 (fun _ => rfl) (fun l => ?_)
  have hl := l.isLt
  have hr := rF a NI o hNI l
  have hv : (slF NI o l).val = fF NI o l.val := vmap_val (bF a NI o hNI) l
  unfold need at hNI
  by_cases h1 : l.val < 17
  · have e : l = src ⟨l.val, h1⟩ := Fin.ext (by simp [src])
    have e2 : slF NI o l = wp NI (2 + o + l.val) := by
      show wp NI (fF NI o l.val) = _
      unfold fF; rw [if_pos h1]
    have e3 : ExtIncidence.NativeFanout.input data R l = data ⟨l.val, h1⟩ :=
      (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_src data R _)
    rw [e2, e3]; exact hs ⟨l.val, h1⟩
  · by_cases h2 : l.val < 526
    · have e : l = dst ⟨l.val - 17, by omega⟩ := Fin.ext (by simp [dst]; omega)
      have e3 : ExtIncidence.NativeFanout.input data R l = [] :=
        (congrArg (ExtIncidence.NativeFanout.input data R) e).trans (in_dst data R _)
      rw [e3]
      refine hb _ hr ?_ ?_ <;> rw [hv] <;> unfold fF <;> split_ifs <;> omega
    · by_cases h3 : l.val = 526
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
    (hb : ∀ x : Fin (2 + rowsWork NI),
      R3 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val →
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
    (h0 : A3 (wp NI (2 + o + 21)) = List.replicate (sv / 2) true)
    (h1 : A3 (wp NI (2 + o + 22)) = List.replicate ((sv + 1) / 2) true)
    (h2 : A3 (wp NI (2 + o + 23)) = List.replicate sv true)
    (hb : ∀ x : Fin (2 + rowsWork NI),
      R4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val →
      ¬ (2 + o + 21 ≤ x.val ∧ x.val ≤ 2 + o + 23) → A3 x = []) :
    ∃ B : Fin (RowsInit.LoopTable.N + 1) → List Bool,
      Step (m4 a NI o) (2 * RowsInit.LoopTable.tableCost sv + 2) (fun _ => 0) A3 (fun _ => 0)
        (install (sl4 a NI o) A3 B) ∧
      B ⟨3, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^(sv/2)) ∧
      B ⟨4, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word (2^((sv+1)/2)) ∧
      B ⟨5, by decide⟩ = List.replicate (2^sv) true ∧ B ⟨6, by decide⟩ = List.replicate (2*2^sv+1) false ∧
      B ⟨7, by decide⟩ = List.replicate (2^sv) false := by
  obtain ⟨B, h, c3, c4, c5, c6, c7⟩ := RowsInit.ThrLoop.table_masked sv
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
    have ew : ∀ v, l.val = v → sl4 a NI o l = wp NI (f4 NI o (RowsInit.SymLoopWords.symVec a).extra
        (RowsInit.LoopAux.auxVec a).extra v) := by intro v hv'; show wp NI _ = _; rw [hv']
    by_cases l0 : l.val = 0
    · rw [ew 0 l0, show f4 NI o _ _ 0 = 2 + o + 21 by simp [f4], h0]; simp [RowsInit.LoopTable.tin, l0]
    by_cases l1 : l.val = 1
    · rw [ew 1 l1, show f4 NI o _ _ 1 = 2 + o + 22 by simp [f4], h1]; simp [RowsInit.LoopTable.tin, l1]
    by_cases l2 : l.val = 2
    · rw [ew 2 l2, show f4 NI o _ _ 2 = 2 + o + 23 by simp [f4], h2]; simp [RowsInit.LoopTable.tin, l2]
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

/-! ## 6. The source words fit the capacity (`sym_hml` at witnessing ports) -/

def wit : Fin 17 → Fin 254 := ![2, 3, 4, 5, 6, 7, 105, 108, 112, 124, 128, 135, 136, 137, 138, 139, 144]

theorem wit_sel : ∀ j, symSel (wit j) = some j := by decide
theorem wit_key : ∀ j, wit j ∉ symKeyPorts := by decide

theorem src_len (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k0 : RCFive.RowKeys.SymKey r L target) (j : Fin 17) :
    (symSrcOf a (.sym r four L target) j).length ≤ symRes r.q (symT a r four L target) := by
  have h1 := master_fan a r four L target k0 (wit j) (Or.inl (wit_key j))
  have h2 := sym_hml a r four L target (symRes r.q (symT a r four L target)) (symR_le_res _ _) k0 (wit j)
  rw [h1, wit_sel j] at h2
  simp only [Option.elim, ZeroPadding.pad_length] at h2
  omega

theorem symKeyPorts_iff : ∀ k : Fin 254, k ∈ symKeyPorts ↔ (k.val = 109 ∨ isKey k.val) := by
  intro k
  unfold isKey symKeyPorts
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  constructor
  · intro h
    simp at h
    omega
  · intro h
    have : k.val = 109 ∨ k.val = 140 ∨ k.val = 141 ∨ k.val = 142 ∨ k.val = 143 := by omega
    simpa using this

theorem dst_val (v : ℕ) (h : v < 509) : (dst ⟨v, h⟩).val = 17 + v := by simp [dst]

/-! ## 7. The chained banks, port by port -/

section Banks
variable (a : DecompositionAlgorithm) (NI o : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
  (B1 : Fin (1 + 18 + (RowsInit.SymLoopWords.symVec a).extra + 1) → List Bool) (data : Fin 17 → List Bool) (R : ℕ)
  (B3 : Fin (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1) → List Bool) (B4 : Fin (RowsInit.LoopTable.N + 1) → List Bool)

def bk1 := install (sl1 a NI o) A B1
def bk2 := install (slF NI o) (bk1 a NI o A B1) (ExtIncidence.NativeFanout.output fanSel data R)
def bk3 := install (sl3 a NI o) (bk2 a NI o A B1 data R) B3
def bk4 := install (sl4 a NI o) (bk3 a NI o A B1 data R B3) B4

variable (hNI : o + need a ≤ NI)
include hNI

theorem bk1_out (x : Fin (2 + rowsWork NI)) (h1 : ¬ R1 NI o (RowsInit.SymLoopWords.symVec a).extra x.val) :
    bk1 a NI o A B1 x = A x := inst_out _ _ _ x _ (r1 a NI o hNI) h1
theorem bk2_out (x : Fin (2 + rowsWork NI)) (hF : ¬ RF NI o x.val) :
    bk2 a NI o A B1 data R x = bk1 a NI o A B1 x := inst_out _ _ _ x _ (rF a NI o hNI) hF
theorem bk3_out (x : Fin (2 + rowsWork NI))
    (h3 : ¬ R3 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk3 a NI o A B1 data R B3 x = bk2 a NI o A B1 data R x := inst_out _ _ _ x _ (r3 a NI o hNI) h3
theorem bk4_out (x : Fin (2 + rowsWork NI))
    (h4 : ¬ R4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = bk3 a NI o A B1 data R B3 x := inst_out _ _ _ x _ (r4 a NI o hNI) h4

theorem bk4_F (x : Fin (2 + rowsWork NI)) (l : Fin (17 + (509 + 1) + 1)) (hx : x.val = fF NI o l.val)
    (h4 : ¬ R4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (h3 : ¬ R3 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = ExtIncidence.NativeFanout.output fanSel data R l := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4, bk3_out a NI o A B1 data R B3 hNI x h3,
    show x = slF NI o l from Fin.ext (hx.trans (vmap_val (bF a NI o hNI) l).symm)]
  exact install_slot _ (injF a NI o hNI) _ _ _

theorem bk4_3 (x : Fin (2 + rowsWork NI)) (l : Fin (1 + 9 + (RowsInit.LoopAux.auxVec a).extra + 1))
    (hx : x.val = f3 NI o (RowsInit.SymLoopWords.symVec a).extra l.val)
    (h4 : ¬ R4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = B3 l := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4,
    show x = sl3 a NI o l from Fin.ext (hx.trans (vmap_val (b3 a NI o hNI) l).symm)]
  exact install_slot _ (inj3 a NI o hNI) _ _ _

theorem bk4_4 (x : Fin (2 + rowsWork NI)) (l : Fin (RowsInit.LoopTable.N + 1))
    (hx : x.val = f4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra l.val) :
    bk4 a NI o A B1 data R B3 B4 x = B4 l := by
  rw [show x = sl4 a NI o l from Fin.ext (hx.trans (vmap_val (b4 a NI o hNI) l).symm)]
  exact install_slot _ (inj4 a NI o hNI) _ _ _

theorem bk_all (x : Fin (2 + rowsWork NI))
    (h4 : ¬ R4 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (h3 : ¬ R3 NI o (RowsInit.SymLoopWords.symVec a).extra (RowsInit.LoopAux.auxVec a).extra x.val)
    (hF : ¬ RF NI o x.val) (h1 : ¬ R1 NI o (RowsInit.SymLoopWords.symVec a).extra x.val) :
    bk4 a NI o A B1 data R B3 B4 x = A x := by
  rw [bk4_out a NI o A B1 data R B3 B4 hNI x h4, bk3_out a NI o A B1 data R B3 hNI x h3,
    bk2_out a NI o A B1 data R hNI x hF, bk1_out a NI o A B1 hNI x h1]

end Banks

/-! ## 8. The run -/

section Run
variable (a : DecompositionAlgorithm) (NI o : ℕ) (hNI : o + need a ≤ NI)
include hNI

theorem chain (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k0 : RCFive.RowKeys.SymKey r L target) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.sym r four L target)))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ B1 B3 B4, Step (machine a NI o) (cost a (.sym r four L target)) (fun _ => 0) A (fun _ => 0)
        (bk4 a NI o A B1 (symSrcOf a (.sym r four L target)) (symRes r.q (symT a r four L target)) B3 B4) ∧
      B3 ⟨0, by omega⟩ = frame (Request.input a (.sym r four L target)) ∧
      B3 ⟨1, by omega⟩ = frame (SignedSortKey.binary ((RowsInit.LoopAux.sOf a (.sym r four L target) + 1) / 2) 0) ∧
      B3 ⟨2, by omega⟩ = frame (SignedSortKey.binary (RowsInit.LoopAux.sOf a (.sym r four L target) / 2) 0) ∧
      B3 ⟨3, by omega⟩ = List.replicate (loopCl r.q) false ∧
      B3 ⟨4, by omega⟩ = List.replicate (loopDl r.q) false ∧
      B3 ⟨5, by omega⟩ = CloseoutRowsGateSupport.gateMembers
        (PCJ9eff70d512234a4c_Fixed.Packets.live ((Request.sym r four L target).family a))ᶜ ∧
      B3 ⟨6, by omega⟩ = RepairSource.VerifierDecoding.CompareMachine.word r.q ∧
      B4 ⟨3, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word
        (2^(RowsInit.LoopAux.sOf a (.sym r four L target)/2)) ∧
      B4 ⟨4, by decide⟩ = RepairSource.VerifierDecoding.CompareMachine.word
        (2^((RowsInit.LoopAux.sOf a (.sym r four L target)+1)/2)) ∧
      B4 ⟨5, by decide⟩ = List.replicate (2^RowsInit.LoopAux.sOf a (.sym r four L target)) true ∧
      B4 ⟨6, by decide⟩ = List.replicate (2*2^RowsInit.LoopAux.sOf a (.sym r four L target)+1) false ∧
      B4 ⟨7, by decide⟩ = List.replicate (2^RowsInit.LoopAux.sOf a (.sym r four L target)) false := by
  have hn := hNI
  unfold need at hn
  have i1 := inj1 a NI o hNI
  have i3 := inj3 a NI o hNI
  obtain ⟨B1, s1, b10, b1s, b1c⟩ := st1 a NI o hNI (.sym r four L target) A h0 hI hL
  have s2 := stF a NI o hNI (symSrcOf a (.sym r four L target)) (symRes r.q (symT a r four L target))
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
  obtain ⟨B3, s3, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39⟩ := st3 a NI o hNI (.sym r four L target)
    (bk2 a NI o A B1 (symSrcOf a (.sym r four L target)) (symRes r.q (symT a r four L target))) (by
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
  have e3 : ∀ m : ℕ, (h1 : 7 ≤ m) → (h2 : m ≤ 9) → wp NI (2 + o + 14 + m) = sl3 a NI o ⟨m, by omega⟩ := by
    intro m h1 h2; show _ = wp NI (f3 NI o _ m); congr 1; unfold f3; split_ifs <;> omega
  obtain ⟨B4, s4, c3, c4, c5, c6, c7⟩ := st4 a NI o hNI (RowsInit.LoopAux.sOf a (.sym r four L target))
    (bk3 a NI o A B1 (symSrcOf a (.sym r four L target)) (symRes r.q (symT a r four L target)) B3)
    (by unfold bk3; rw [show 2 + o + 21 = 2 + o + 14 + 7 by omega, e3 7 (by omega) (by omega), install_slot _ i3]; exact b37)
    (by unfold bk3; rw [show 2 + o + 22 = 2 + o + 14 + 8 by omega, e3 8 (by omega) (by omega), install_slot _ i3]; exact b38)
    (by unfold bk3; rw [show 2 + o + 23 = 2 + o + 14 + 9 by omega, e3 9 (by omega) (by omega), install_slot _ i3]; exact b39)
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

/-- **The SYM loop block and C6 words of `symBase 0`** (the four key masters left blank, the entry form of RC5's key-0
writer `KeyZeroMode.sym_k0`), from a work bank whose request port holds the framed request and whose loop/C6 blocks and
init region `[o, o + need a)` are blank; every other port is untouched. `k₀` is any key (the non-key masters do not
depend on it). -/
theorem loop_run (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k0 : RCFive.RowKeys.SymKey r L target) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.sym r four L target)))
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need a → A x = [])
    (hL : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a NI o) (cost a (.sym r four L target)) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k ∈ symKeySet, A' (masterPort NI k) = []) ∧
      (∀ i : Fin (MT+1+1), (∀ k ∈ symKeySet, loopPort NI i ≠ masterPort NI k) →
        A' (loopPort NI i) = loopBank (symLive r L) (symRes r.q (symT a r four L target))
          (symMasters a r four L target (symRes r.q (symT a r four L target)) k0) i) ∧
      (∀ i, A' (c6Port NI i) = c6Words (symLive r L)ᶜ.card i) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 + o ≤ x.val ∧ x.val < 2 + o + need a) →
        ¬ (2 + NI + 72 ≤ x.val ∧ x.val < 2 + NI + 594) → A' x = A x) := by
  have hn := hNI
  unfold need at hn
  have hneed : need a = 88 + (RowsInit.SymLoopWords.symVec a).extra + (RowsInit.LoopAux.auxVec a).extra := rfl
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
    · rw [RowsInit.ThrLoop.lb_lt _ _ _ v hv (by simp [MT]; omega),
        RowsInit.ThrLoop.tp_cell _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) hc]
      by_cases hc1 : v < 254
      · rw [RowsInit.ThrLoop.vf_lt _ _ _ v hc hc1, bk4_F a NI o A B1 _ _ B3 B4 hNI _ (dst ⟨v, by omega⟩)
          (by rw [hvx, dst_val]; unfold fF; split_ifs <;> omega) (by unfold R4; omega) (by unfold R3; omega),
          out_blank _ _ _ (Or.inl hc1)]
      · rw [RowsInit.ThrLoop.vf_hi _ _ _ v hc (by omega)]
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
    · rw [RowsInit.ThrLoop.lb_lt _ _ _ v hv (by simp [MT]; omega),
        RowsInit.ThrLoop.tp_master _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) (by omega) hm]
      have hnk : ¬ isKey (v - 257) := by
        intro hk
        have hkk : (⟨v - 257, by omega⟩ : Fin 254) ∈ symKeySet := (isKey_iff _).1 hk
        exact hi _ hkk (Fin.ext (by rw [hvx, master_val]; simp; omega))
      rw [bk4_F a NI o A B1 _ _ B3 B4 hNI _ (dst ⟨254 + (v - 257), by omega⟩) (by
          rw [hvx, dst_val]; unfold fF; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          rw [if_neg (by rw [show 17 + (254 + (v - 257)) - 271 = v - 257 by omega]; exact hnk)]; omega)
        (by unfold R4; omega) (by unfold R3; omega)]
      rw [out_master _ _ ⟨v - 257, by omega⟩]
      by_cases h109 : v - 257 = 109
      · rw [master_fan a r four L target k0 _ (Or.inr (Fin.ext h109))]
      · rw [master_fan a r four L target k0 _ (Or.inl (by
          rw [symKeyPorts_iff]; intro h; rcases h with h | h
          · exact h109 h
          · exact hnk h))]
    by_cases ha : v < 518
    · rw [RowsInit.ThrLoop.lb_lt _ _ _ v hv (by simp [MT]; omega),
        RowsInit.ThrLoop.tp_aux _ _ _ _ _ _ _ _ _ v (by simp [MT]; omega) (by omega)]
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
      rw [RowsInit.ThrLoop.lb_c0 _ _ _ _ (by simp [MT]),
        bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨3, by decide⟩ (by rw [hvx]; simp [f4]), c3]; rfl
    have h519 : v = 519 := by omega
    subst h519
    rw [RowsInit.ThrLoop.lb_c1 _ _ _ _ (by simp [MT]),
      bk4_4 a NI o A B1 _ _ B3 B4 hNI _ ⟨4, by decide⟩ (by rw [hvx]; simp [f4]), c4]; rfl
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
end RowsInit.SymLoop
