import Proof.Packets.PacketsSeedDrivers
import Proof.Packets.PacketsCoordHoles

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent
open NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

variable {a : DecompositionAlgorithm}

/-- Transport a key word along a pointwise equality of values. -/
def KeyWord.congrV {v w : ∀ r : Request, rcKey a r → List Bool} (s : KeyWord a v) (h : ∀ r k, v r k = w r k) :
    KeyWord a w where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  costC := s.costC
  costD := s.costD
  cost_le := s.cost_le
  run := fun r k hk => by
    obtain ⟨H, A, st, hkeep, h9, h9H⟩ := s.run r k hk
    exact ⟨H, A, st, hkeep, h9.trans (h r k), h9H⟩

section Key
variable (ls : UnaryStage a (fun r => (walkLength a r - 1) * 160))
variable (ss : WordStage a (fun r => CompareMachine.word (rank a r * 3 / 2)))

/-- The key word's private tape count. -/
def keyExtra : ℕ := 6 + ls.extra + ss.extra

def lsSlot (j : Fin (2 + ls.extra)) : Fin (10 + keyExtra ls ss) :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 10 else j.val + 14, by
    have := j.isLt; unfold keyExtra; split_ifs <;> omega⟩

def ssSlot (j : Fin (2 + ss.extra)) : Fin (10 + keyExtra ls ss) :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 11 else j.val + 14 + ls.extra, by
    have := j.isLt; unfold keyExtra; split_ifs <;> omega⟩

def seedSlot (o : Fin 3) (j : Fin 7) : Fin (10 + keyExtra ls ss) :=
  ⟨if j.val = 0 then 6 else if j.val = 1 then 10 else if j.val = 2 then 11 else if j.val = 6 then 15
    else if j.val = 3 + o.val then 9 else j.val + 9, by
    have := j.isLt; unfold keyExtra; split_ifs <;> omega⟩

theorem lsSlot_val (j : Fin (2 + ls.extra)) :
    (lsSlot ls ss j).val = if j.val = 0 then 0 else if j.val = 1 then 10 else j.val + 14 := rfl
theorem ssSlot_val (j : Fin (2 + ss.extra)) :
    (ssSlot ls ss j).val = if j.val = 0 then 0 else if j.val = 1 then 11 else j.val + 14 + ls.extra := rfl
theorem seedSlot_val (o : Fin 3) (j : Fin 7) :
    (seedSlot ls ss o j).val = if j.val = 0 then 6 else if j.val = 1 then 10 else if j.val = 2 then 11
      else if j.val = 6 then 15 else if j.val = 3 + o.val then 9 else j.val + 9 := rfl

theorem lsSlot_inj : Function.Injective (lsSlot ls ss) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [lsSlot_val, lsSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem ssSlot_inj : Function.Injective (ssSlot ls ss) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [ssSlot_val, ssSlot_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem seedSlot_inj (o : Fin 3) : Function.Injective (seedSlot ls ss o) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [seedSlot_val, seedSlot_val] at hv
  have := o.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The key word's machine for output `o`. -/
def keyMachine (o : Fin 3) :=
  Composition.machine (RecoveryFocus.machine (lsSlot ls ss) ls.machine)
    (Composition.machine (RecoveryFocus.machine (ssSlot ls ss) ss.machine)
      (RecoveryFocus.machine (seedSlot ls ss o) readyMachine))

/-- The seed split's fuel at request level. -/
def seedCostR (r : Request) : ℕ := 2 * ((walkLength a r - 1) * 160) + 4 * (rank a r * 3 / 2) + 3

def keyCost (r : Request) : ℕ := ls.cost r + 1 + (ss.cost r + 1 + (2 * seedCostR (a := a) r + 2))

theorem readyEntry_val {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den W : ℕ)
    (sample : LiveRows.Seed occ I den) (j : Fin 7) :
    readyEntry occ I den W sample j =
      if j.val = 0 then seedField occ I den W sample else if j.val = 1 then List.replicate (labelBits den) true
      else if j.val = 2 then CompareMachine.word (MaskCoord.side occ I) else [] := by
  fin_cases j <;> rfl

section Stages
variable (r : Request) (M : Fin (10 + keyExtra ls ss) → List Bool)

/-- Stage 1 (the label driver on tape 10). -/
theorem stage1 (hM0 : M ⟨0, by (try unfold keyExtra); omega⟩ = RepairOrdinary.frame (Request.input a r))
    (hMhi : ∀ i : Fin (10 + keyExtra ls ss), 9 ≤ i.val → M i = []) : ∃ (HA : Fin (10 + keyExtra ls ss) → ℕ) (AA : Fin (10 + keyExtra ls ss) → List Bool),
    Step (RecoveryFocus.machine (lsSlot ls ss) ls.machine) (ls.cost r) (fun _ => 0) M HA AA ∧
    AA ⟨0, by (try unfold keyExtra); omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ HA ⟨0, by (try unfold keyExtra); omega⟩ = 0 ∧
    AA ⟨10, by (try unfold keyExtra); omega⟩ = List.replicate ((walkLength a r - 1) * 160) true ∧ HA ⟨10, by (try unfold keyExtra); omega⟩ = 0 ∧
    ∀ i : Fin (10 + keyExtra ls ss), i.val ≠ 0 → i.val ≠ 10 → (i.val < 16 ∨ 16 + ls.extra ≤ i.val) →
      AA i = M i ∧ HA i = 0 := by
  obtain ⟨H1, A1, s1, a10, h10, a11, h11⟩ := ls.run r
  obtain ⟨HA, AA, st1, hs1, ho1⟩ := Dock.lift s1 (lsSlot ls ss) (lsSlot_inj ls ss) (fun _ => 0) (fun _ => 0) M (by
    intro j
    refine ⟨rfl, ?_⟩
    rw [ZeroPadding.pad_zero]
    by_cases h0 : j.val = 0
    · have e : lsSlot ls ss j = ⟨0, by (try unfold keyExtra); omega⟩ := Fin.ext (by rw [lsSlot_val]; simp [h0])
      rw [e, hM0]; simp [inBank, h0]
    · rw [hMhi _ (by rw [lsSlot_val]; split_ifs <;> omega)]; simp [inBank, h0])
  have e0 : (⟨0, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = lsSlot ls ss ⟨0, by omega⟩ :=
    Fin.ext (by rw [lsSlot_val]; rfl)
  have e1 : (⟨10, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = lsSlot ls ss ⟨1, by omega⟩ :=
    Fin.ext (by rw [lsSlot_val]; rfl)
  refine ⟨HA, AA, st1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, (hs1 _).2, ZeroPadding.pad_zero]; exact a10
  · rw [e0, (hs1 _).1]; exact h10
  · rw [e1, (hs1 _).2, ZeroPadding.pad_zero]; exact a11
  · rw [e1, (hs1 _).1]; exact h11
  · intro i h0 h10' h16
    have hn : ∀ j, lsSlot ls ss j ≠ i := by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [lsSlot_val] at hv
      have := j.isLt
      split_ifs at hv <;> omega
    exact ⟨(ho1 i hn).2, (ho1 i hn).1⟩

/-- Stage 2 (the side counter on tape 11). -/
theorem stage2 (hMhi : ∀ i : Fin (10 + keyExtra ls ss), 9 ≤ i.val → M i = [])
    (HA : Fin (10 + keyExtra ls ss) → ℕ) (AA : Fin (10 + keyExtra ls ss) → List Bool)
    (hA0 : AA ⟨0, by (try unfold keyExtra); omega⟩ = RepairOrdinary.frame (Request.input a r)) (hH0 : HA ⟨0, by (try unfold keyExtra); omega⟩ = 0)
    (hclean : ∀ i : Fin (10 + keyExtra ls ss), i.val ≠ 0 → i.val ≠ 10 → (i.val < 16 ∨ 16 + ls.extra ≤ i.val) →
      AA i = M i ∧ HA i = 0) :
    ∃ (HB : Fin (10 + keyExtra ls ss) → ℕ) (AB : Fin (10 + keyExtra ls ss) → List Bool),
    Step (RecoveryFocus.machine (ssSlot ls ss) ss.machine) (ss.cost r) HA AA HB AB ∧
    AB ⟨0, by (try unfold keyExtra); omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ HB ⟨0, by (try unfold keyExtra); omega⟩ = 0 ∧
    AB ⟨11, by (try unfold keyExtra); omega⟩ = CompareMachine.word (rank a r * 3 / 2) ∧ HB ⟨11, by (try unfold keyExtra); omega⟩ = 0 ∧
    ∀ i : Fin (10 + keyExtra ls ss), i.val ≠ 0 → i.val ≠ 11 → i.val < 16 → AB i = AA i ∧ HB i = HA i := by
  obtain ⟨H2, A2, s2, a20, h20, a21, h21⟩ := ss.run r
  obtain ⟨HB, AB, st2, hs2, ho2⟩ := Dock.lift s2 (ssSlot ls ss) (ssSlot_inj ls ss) (fun _ => 0) HA AA (by
    intro j
    rw [ZeroPadding.pad_zero]
    by_cases h0 : j.val = 0
    · have e : ssSlot ls ss j = ⟨0, by (try unfold keyExtra); omega⟩ := Fin.ext (by rw [ssSlot_val]; simp [h0])
      rw [e, hA0, hH0]; simp [inBank, h0]
    · have hc := hclean (ssSlot ls ss j) (by rw [ssSlot_val]; split_ifs <;> omega)
        (by rw [ssSlot_val]; split_ifs <;> omega) (by rw [ssSlot_val]; split_ifs <;> omega)
      rw [hc.1, hc.2, hMhi _ (by rw [ssSlot_val]; split_ifs <;> omega)]
      simp [inBank, h0])
  have e0 : (⟨0, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = ssSlot ls ss ⟨0, by omega⟩ :=
    Fin.ext (by rw [ssSlot_val]; rfl)
  have e1 : (⟨11, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = ssSlot ls ss ⟨1, by omega⟩ :=
    Fin.ext (by rw [ssSlot_val]; rfl)
  refine ⟨HB, AB, st2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, (hs2 _).2, ZeroPadding.pad_zero]; exact a20
  · rw [e0, (hs2 _).1]; exact h20
  · rw [e1, (hs2 _).2, ZeroPadding.pad_zero]; exact a21
  · rw [e1, (hs2 _).1]; exact h21
  · intro i h0 h11' h16
    have hn : ∀ j, ssSlot ls ss j ≠ i := by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [ssSlot_val] at hv
      have := j.isLt
      split_ifs at hv <;> omega
    exact ⟨(ho2 i hn).2, (ho2 i hn).1⟩

/-- Stage 3 (the split, docked; output `3 + o` on tape 9). -/
theorem stage3 (o : Fin 3) {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den W : ℕ)
    (sample : LiveRows.Seed occ I den) (HB : Fin (10 + keyExtra ls ss) → ℕ) (AB : Fin (10 + keyExtra ls ss) → List Bool)
    (h6 : AB ⟨6, by (try unfold keyExtra); omega⟩ = seedField occ I den W sample ∧ HB ⟨6, by (try unfold keyExtra); omega⟩ = 0)
    (h10 : AB ⟨10, by (try unfold keyExtra); omega⟩ = List.replicate (labelBits den) true ∧ HB ⟨10, by (try unfold keyExtra); omega⟩ = 0)
    (h11 : AB ⟨11, by (try unfold keyExtra); omega⟩ = CompareMachine.word (MaskCoord.side occ I) ∧ HB ⟨11, by (try unfold keyExtra); omega⟩ = 0)
    (hblank : ∀ i : Fin (10 + keyExtra ls ss), 9 ≤ i.val → i.val < 16 → i.val ≠ 10 → i.val ≠ 11 →
      AB i = [] ∧ HB i = 0)
    (hW : labelBits den + 2 * MaskCoord.side occ I ≤ W) :
    ∃ (HC : Fin (10 + keyExtra ls ss) → ℕ) (AC : Fin (10 + keyExtra ls ss) → List Bool),
    Step (RecoveryFocus.machine (seedSlot ls ss o) readyMachine) (2 * cost occ I den + 2) HB AB HC AC ∧
    AC ⟨6, by (try unfold keyExtra); omega⟩ = seedField occ I den W sample ∧ HC ⟨6, by (try unfold keyExtra); omega⟩ = 0 ∧
    AC ⟨9, by (try unfold keyExtra); omega⟩ = exit occ I den W sample ⟨3 + o.val, by omega⟩ ∧ HC ⟨9, by (try unfold keyExtra); omega⟩ = 0 ∧
    ∀ i : Fin (10 + keyExtra ls ss), i.val < 9 → i.val ≠ 6 → AC i = AB i ∧ HC i = HB i := by
  have ho := o.isLt
  obtain ⟨kk, s3⟩ := seed_ready occ I den W sample hW
  obtain ⟨HC, AC, st3, hs3, ho3⟩ := Dock.lift s3 (seedSlot ls ss o) (seedSlot_inj ls ss o) (fun _ => 0) HB AB (by
    intro j
    rw [ZeroPadding.pad_zero, readyEntry_val]
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · have e : seedSlot ls ss o j = ⟨6, by (try unfold keyExtra); omega⟩ := Fin.ext (by rw [seedSlot_val]; simp [h0])
      rw [e, h6.1, h6.2]; simp [h0]
    by_cases h1 : j.val = 1
    · have e : seedSlot ls ss o j = ⟨10, by (try unfold keyExtra); omega⟩ := Fin.ext (by rw [seedSlot_val]; simp [h1])
      rw [e, h10.1, h10.2]; simp [h1]
    by_cases h2 : j.val = 2
    · have e : seedSlot ls ss o j = ⟨11, by (try unfold keyExtra); omega⟩ := Fin.ext (by rw [seedSlot_val]; simp [h2])
      rw [e, h11.1, h11.2]; simp [h2]
    have hb := hblank (seedSlot ls ss o j) (by rw [seedSlot_val]; split_ifs <;> omega)
      (by rw [seedSlot_val]; split_ifs <;> omega) (by rw [seedSlot_val]; split_ifs <;> omega)
      (by rw [seedSlot_val]; split_ifs <;> omega)
    rw [hb.1, hb.2]
    simp [h0, h1, h2])
  have e6 : (⟨6, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = seedSlot ls ss o ⟨0, by omega⟩ :=
    Fin.ext (by rw [seedSlot_val]; rfl)
  have e9 : (⟨9, by (try unfold keyExtra); omega⟩ : Fin (10 + keyExtra ls ss)) = seedSlot ls ss o ⟨3 + o.val, by omega⟩ :=
    Fin.ext (by rw [seedSlot_val]; simp only; split_ifs <;> omega)
  refine ⟨HC, AC, st3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e6, (hs3 _).2, ZeroPadding.pad_zero]; rfl
  · rw [e6, (hs3 _).1]
  · rw [e9, (hs3 _).2, ZeroPadding.pad_zero]
    have hlt : 3 + o.val < 6 := by omega
    change readyExit occ I den W sample kk ⟨3 + o.val, by omega⟩ = _
    unfold readyExit
    rw [show (⟨3 + o.val, by omega⟩ : Fin (6 + 1)) = Fin.castAdd 1 ⟨3 + o.val, hlt⟩ from rfl, Fin.addCases_left]
  · rw [e9, (hs3 _).1]
  · intro i h9 h6'
    have hn : ∀ j, seedSlot ls ss o j ≠ i := by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [seedSlot_val] at hv
      have := j.isLt
      split_ifs at hv <;> omega
    exact ⟨(ho3 i hn).2, (ho3 i hn).1⟩

end Stages

/-- **The generic run**, at any seed field meeting the four identities. -/
theorem key_run (o : Fin 3) (r : Request) (k : rcKey a r) {q : ℕ} (occ : List (SupportedNormalizedGate q))
    (I : Finset (Fin q)) (den W : ℕ) (sample : LiveRows.Seed occ I den)
    (hF : PacketsCombine.metaEntry a r (some k) (10 + keyExtra ls ss) ⟨6, by (try unfold keyExtra); omega⟩ =
      seedField occ I den W sample)
    (hL : (walkLength a r - 1) * 160 = labelBits den) (hS : rank a r * 3 / 2 = MaskCoord.side occ I)
    (hW : labelBits den + 2 * MaskCoord.side occ I ≤ W) :
    ∃ (H : Fin (10 + keyExtra ls ss) → ℕ) (A : Fin (10 + keyExtra ls ss) → List Bool),
      Step (keyMachine ls ss o) (keyCost ls ss r) (fun _ => 0)
        (PacketsCombine.metaEntry a r (some k) (10 + keyExtra ls ss)) H A ∧
      (∀ i : Fin (10 + keyExtra ls ss), i.val < 9 →
        A i = PacketsCombine.metaEntry a r (some k) (10 + keyExtra ls ss) i ∧ H i = 0) ∧
      A ⟨9, by (try unfold keyExtra); omega⟩ = exit occ I den W sample ⟨3 + o.val, by omega⟩ ∧
      H ⟨9, by (try unfold keyExtra); omega⟩ = 0 := by
  set M := PacketsCombine.metaEntry a r (some k) (10 + keyExtra ls ss) with hM
  have hMhi : ∀ i : Fin (10 + keyExtra ls ss), 9 ≤ i.val → M i = [] := by
    intro i hi
    simp only [hM, PacketsCombine.metaEntry]
    rw [if_neg (by omega), dif_neg (by omega)]
  have hM0 : M ⟨0, by (try unfold keyExtra); omega⟩ = RepairOrdinary.frame (Request.input a r) := by
    simp only [hM, PacketsCombine.metaEntry]; rfl
  obtain ⟨HA, AA, st1, a0, h0, a10, h10, c1⟩ := stage1 ls ss r M hM0 hMhi
  obtain ⟨HB, AB, st2, b0, hb0, b11, hb11, c2⟩ := stage2 ls ss r M hMhi HA AA a0 h0 c1
  have h6 : AB ⟨6, by (try unfold keyExtra); omega⟩ = seedField occ I den W sample ∧
      HB ⟨6, by (try unfold keyExtra); omega⟩ = 0 := by
    have e2 := c2 ⟨6, by (try unfold keyExtra); omega⟩ (by simp) (by simp) (by simp)
    have e1 := c1 ⟨6, by (try unfold keyExtra); omega⟩ (by simp) (by simp) (by simp)
    rw [e2.1, e2.2, e1.1, e1.2, hF]
    exact ⟨rfl, rfl⟩
  have h10' : AB ⟨10, by (try unfold keyExtra); omega⟩ = List.replicate (labelBits den) true ∧
      HB ⟨10, by (try unfold keyExtra); omega⟩ = 0 := by
    have e2 := c2 ⟨10, by (try unfold keyExtra); omega⟩ (by simp) (by simp) (by simp)
    rw [e2.1, e2.2, a10, h10, hL]
    exact ⟨rfl, rfl⟩
  have h11' : AB ⟨11, by (try unfold keyExtra); omega⟩ = CompareMachine.word (MaskCoord.side occ I) ∧
      HB ⟨11, by (try unfold keyExtra); omega⟩ = 0 := by
    rw [b11, hb11, hS]
    exact ⟨rfl, rfl⟩
  have hblank : ∀ i : Fin (10 + keyExtra ls ss), 9 ≤ i.val → i.val < 16 → i.val ≠ 10 → i.val ≠ 11 →
      AB i = [] ∧ HB i = 0 := by
    intro i h9 h16 h10'' h11''
    have e2 := c2 i (by omega) h11'' h16
    have e1 := c1 i (by omega) h10'' (by omega)
    rw [e2.1, e2.2, e1.1, e1.2, hMhi i h9]
    exact ⟨rfl, rfl⟩
  obtain ⟨HC, AC, st3, c6, hc6, c9, hc9, c3⟩ := stage3 ls ss o occ I den W sample HB AB h6 h10' h11' hblank hW
  have hcost : keyCost ls ss r = ls.cost r + 1 + (ss.cost r + 1 + (2 * cost occ I den + 2)) := by
    unfold keyCost seedCostR cost
    rw [hL, hS]
  refine ⟨HC, AC, ?_, ?_, c9, hc9⟩
  · rw [hcost]
    exact st1.seq (st2.seq st3)
  · intro i hi
    by_cases h6' : i.val = 6
    · have e : i = ⟨6, by (try unfold keyExtra); omega⟩ := Fin.ext h6'
      rw [e, c6, hc6, hF]
      exact ⟨rfl, rfl⟩
    · have e3 := c3 i hi h6'
      rw [e3.1, e3.2]
      by_cases h0' : i.val = 0
      · have e : i = ⟨0, by (try unfold keyExtra); omega⟩ := Fin.ext h0'
        rw [e, b0, hb0, hM0]
        exact ⟨rfl, rfl⟩
      · have e2 := c2 i h0' (by omega) (by omega)
        have e1 := c1 i h0' (by omega) (by omega)
        rw [e2.1, e2.2, e1.1, e1.2]
        exact ⟨rfl, rfl⟩

/-- The key field 5 of `metaEntry` is the seed field (SYM). -/
theorem sym_field (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : rcKey a (.sym r0 four L target)) :
    PacketsCombine.metaEntry a (.sym r0 four L target) (some k) (10 + keyExtra ls ss)
        ⟨6, by (try unfold keyExtra); omega⟩ =
      seedField (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L)
        (symmetricListDenominator r0 target) (PacketsConstruction.fieldWidth a (.sym r0 four L target))
        (show RCFive.RowKeys.SymKey r0 L target from k).seed := by
  have e : PacketsCombine.metaEntry a (.sym r0 four L target) (some k) (10 + keyExtra ls ss)
      ⟨6, by (try unfold keyExtra); omega⟩ = PacketsCombine.keyWord a (.sym r0 four L target) (some k) ⟨5, by omega⟩ := rfl
  rw [e]
  unfold PacketsCombine.keyWord
  rw [keyDigits_sym, dif_neg (by simp; omega), if_pos rfl]
  rfl

/-- The key field 5 of `metaEntry` is the seed field (THR). -/
theorem thr_field (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) (k : rcKey a (.thr r0 four L target)) :
    PacketsCombine.metaEntry a (.thr r0 four L target) (some k) (10 + keyExtra ls ss)
        ⟨6, by (try unfold keyExtra); omega⟩ =
      seedField (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
        (PacketsConstruction.fieldWidth a (.thr r0 four L target))
        (show RCFive.RowKeys.ThrKey a r0 L target from k).seed := by
  have e : PacketsCombine.metaEntry a (.thr r0 four L target) (some k) (10 + keyExtra ls ss)
      ⟨6, by (try unfold keyExtra); omega⟩ = PacketsCombine.keyWord a (.thr r0 four L target) (some k) ⟨5, by omega⟩ := rfl
  rw [e]
  unfold PacketsCombine.keyWord
  rw [keyDigits_thr, dif_neg (by simp; omega), if_neg (by simp), if_pos rfl]
  rfl

/-- The seed outputs per key (`o = 0`: labels, `1`: `startY`, `2`: `startX`). -/
def seedOut (o : Fin 3) : ∀ r : Request, rcKey a r → List Bool
  | .terminal, k => PEmpty.elim k
  | .sym r0 four L target, k => exit (symmetricFourfoldOccurrences r0)
      (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) (symmetricListDenominator r0 target)
      (PacketsConstruction.fieldWidth a (.sym r0 four L target)) (show RCFive.RowKeys.SymKey r0 L target from k).seed
      ⟨3 + o.val, by omega⟩
  | .thr r0 four L target, k => exit (thresholdFourfoldOccurrences r0)
      (CyclicChoice.live (thresholdFourfoldOccurrences r0) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
      (PacketsConstruction.fieldWidth a (.thr r0 four L target)) (show RCFive.RowKeys.ThrKey a r0 L target from k).seed
      ⟨3 + o.val, by omega⟩

/-- The key word's cost bound's degree and coefficient. -/
def keyD : ℕ := ls.degree + ss.degree + (rankStage a).degree + 2
def keyC : ℕ := ls.coefficient + ss.coefficient + 4 * (ls.coefficient + 7) + 16 * ((rankStage a).coefficient + 7) + 20

theorem keyCost_le (r : Request) : keyCost ls ss r ≤ keyC ls ss * (r.smallSize a) ^ keyD ls ss := by
  have s1 := ls.cost_le r
  have s2 := ss.cost_le r
  have v1 : (walkLength a r - 1) * 160 + 3 ≤ (ls.coefficient + 7) * (r.smallSize a) ^ (ls.degree + 1) :=
    ls.value_bound r
  have v2 := (rankStage a).value_bound r
  have hS := one_le_small a r
  set S := r.smallSize a
  have p1 : S ^ ls.degree ≤ S ^ keyD ls ss := Nat.pow_le_pow_right hS (by unfold keyD; omega)
  have p2 : S ^ ss.degree ≤ S ^ keyD ls ss := Nat.pow_le_pow_right hS (by unfold keyD; omega)
  have p3 : S ^ (ls.degree + 1) ≤ S ^ keyD ls ss := Nat.pow_le_pow_right hS (by unfold keyD; omega)
  have p4 : S ^ ((rankStage a).degree + 1) ≤ S ^ keyD ls ss := Nat.pow_le_pow_right hS (by unfold keyD; omega)
  have p0 : 1 ≤ S ^ keyD ls ss := Nat.one_le_pow _ _ hS
  set X := S ^ keyD ls ss
  have q1 := s1.trans (Nat.mul_le_mul_left ls.coefficient p1)
  have q2 := s2.trans (Nat.mul_le_mul_left ss.coefficient p2)
  have q3 := v1.trans (Nat.mul_le_mul_left (ls.coefficient + 7) p3)
  have q4 := v2.trans (Nat.mul_le_mul_left ((rankStage a).coefficient + 7) p4)
  have hr : rank a r * 3 / 2 ≤ 2 * rank a r := by omega
  unfold keyCost seedCostR keyC
  generalize (walkLength a r - 1) * 160 = V1 at q3 ⊢
  generalize rank a r * 3 / 2 = V2 at hr ⊢
  generalize ls.cost r = c1 at q1 ⊢
  generalize ss.cost r = c2 at q2 ⊢
  nlinarith

/-- **The seed decode as one key word** (output `o`). -/
def seedKey (o : Fin 3) : KeyWord a (seedOut o) where
  extra := keyExtra ls ss
  states := _
  machine := keyMachine ls ss o
  cost := keyCost ls ss
  costC := keyC ls ss
  costD := keyD ls ss
  cost_le := keyCost_le ls ss
  run := fun r k _ => by
    cases r with
    | terminal => exact PEmpty.elim k
    | sym r0 four L target =>
      exact key_run ls ss o _ k _ _ _ _ _ (sym_field ls ss r0 four L target k) (sym_label a r0 four L target)
        (sym_side a r0 four L target) (sym_width a r0 four L target)
    | thr r0 four L target =>
      exact key_run ls ss o _ k _ _ _ _ _ (thr_field ls ss r0 four L target k) (thr_label a r0 four L target)
        (thr_side a r0 four L target) (thr_width a r0 four L target)

theorem exit_labels {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den W : ℕ)
    (sample : LiveRows.Seed occ I den) :
    exit occ I den W sample ⟨3 + (0 : Fin 3).val, by omega⟩ = MaskCoord.labelsWord occ I den sample := by
  have e : (⟨3 + (0 : Fin 3).val, by omega⟩ : Fin 6) = ⟨3, by omega⟩ := Fin.ext rfl
  rw [e]
  rfl

/-- **DELIVERABLE: the walk labels word** (`labelsOf`, all-run tape 102). -/
def labelsKey : KeyWord a (labelsOf a) :=
  KeyWord.congrV (seedKey ls ss 0) (fun r k => by
    cases r with
    | terminal => exact PEmpty.elim k
    | sym r0 four L target => exact exit_labels _ _ _ _ _
    | thr r0 four L target => exact exit_labels _ _ _ _ _)

/-- **DELIVERABLE: the start `y` coordinate** (`startYOf`, all-run tape 429). -/
def startYKey : KeyWord a (startYOf a) :=
  KeyWord.congrV (seedKey ls ss 1) (fun r k => by
    cases r with
    | terminal => exact PEmpty.elim k
    | sym => rfl
    | thr => rfl)

/-- **DELIVERABLE: the start `x` coordinate** (`startXOf`, all-run tape 428). -/
def startXKey : KeyWord a (startXOf a) :=
  KeyWord.congrV (seedKey ls ss 2) (fun r k => by
    cases r with
    | terminal => exact PEmpty.elim k
    | sym => rfl
    | thr => rfl)

end Key

end
end NearCubicWires.PacketsSeed

