import Proof.Packets.PacketsKeysNativeStages
import Proof.Rows.RowsInitC5
import Proof.Rows.RowsInitLiveBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.Prefix
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent
open RowsConstruction RowsConstruction.BaseLayout RowsInit.VecDock
open RowsInit.ThrInitRun (inst_at inst_off)
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj rw_eq)
noncomputable section

/-! ## 1. The four words -/

section Words
variable (a : DecompositionAlgorithm)

/-- The row count (RW's `rowsCountStage` at the four input stages of PM / PK). -/
abbrev rowsS : UnaryStage a (fun r => (r.family a).rows.length) :=
  RowsInit.Count.rowsCountStage a (NearCubicWires.PacketsMeta.cutoffStage a) (NearCubicWires.PacketsMeta.Seed.seedCountStage a)
    (NearCubicWires.PacketsMeta.thrSelStage a) (NearCubicWires.PacketsKeys.Native.symSelStage a)

/-- The pool arity `rowpWords` uses: `complCount` on THR/SYM, `0` on the terminal sentinel. -/
def arityOf (r : Request) : ℕ := RowsInit.complCount a r * liveFlag r

/-- The SYM flag value `(1 - thrFlag)·liveFlag`. -/
def symFlag (r : Request) : ℕ := (1 - thrFlag r) * liveFlag r

def pfxWord (j : Fin 4) (r : Request) : List Bool :=
  match j.val with
  | 0 => UnaryTemplate.tape (arityOf a r + 2)
  | 1 => List.replicate (thrFlag r) true
  | 2 => List.replicate (symFlag r) true
  | _ => List.replicate (r.family a).rows.length true

/-- **The prefix words by ONE fixed machine.** -/
def pfxVec :=
  ((((VecStage.nil a (fun _ _ => [])).snoc
    ((((RowsInit.complStage a).pairP (liveFlagStage a) mulMap2 8 2 mul_cost).thenMapP (plusMap 2) (2 * 2 + 4) 1
      (plus_cost 2)).tplP)).snoc (thrFlagStage a).toWord).snoc
    ((notThrStage a).pairP (liveFlagStage a) mulMap2 8 2 mul_cost).toWord).snoc (rowsS a).toWord

end Words

/-! ## 2. Slot maps (values) and their left inverses -/

/-- Vector stage: request, rowp 2, init 146–148, scratch. -/
def h1 (NI oP v : ℕ) : ℕ :=
  if v = 0 then 0 else if v = 1 then 2 + NI + 2 else if v ≤ 4 then 2 + 146 + (v - 2) else 2 + oP + (v - 5)
/-- The unwrap: `pub 1`, `init 149`, its log. -/
def hU (oP e v : ℕ) : ℕ := if v = 0 then 1 else if v = 1 then 2 + 149 else 2 + oP + e + 1
/-- The caps pass: local 0 = `init 149`; the seven `rowp` outputs; every other local `i ↦ rcp i`. -/
def hC (NI v : ℕ) : ℕ :=
  if v = 0 then 2 + 149 else if v = 30 then 2 + NI else if v = 60 then 2 + NI + 1 else if v = 49 then 2 + NI + 3
  else if v = 10 then 2 + NI + 4 else if v = 59 then 2 + NI + 5 else if v = 43 then 2 + NI + 6
  else if v = 45 then 2 + NI + 7 else 2 + NI + 8 + v

def g1 (NI oP x : ℕ) : ℕ :=
  if x = 0 then 0 else if x = 2 + NI + 2 then 1 else if 148 ≤ x ∧ x ≤ 150 then x - 146 else x - (2 + oP) + 5
def gC (NI x : ℕ) : ℕ :=
  if x = 151 then 0 else if x = 2 + NI then 30 else if x = 2 + NI + 1 then 60 else if x = 2 + NI + 3 then 49
  else if x = 2 + NI + 4 then 10 else if x = 2 + NI + 5 then 59 else if x = 2 + NI + 6 then 43
  else if x = 2 + NI + 7 then 45 else x - (2 + NI + 8)

section Maps
variable (a : DecompositionAlgorithm) (NI oP : ℕ)

def needP : ℕ := (pfxVec a).extra + 2
def s1 := vmap NI (1 + 4 + (pfxVec a).extra + 1) (h1 NI oP)
def sU := vmap NI 3 (hU oP ((pfxVec a).extra))
def sC := vmap NI 62 (hC NI)

variable (hT : 150 ≤ oP) (hP : oP + needP a ≤ NI)

include hP in
theorem b1 : ∀ v, v < 1 + 4 + (pfxVec a).extra + 1 → h1 NI oP v < 2 + rowsWork NI := by
  intro v hv; unfold needP at hP; rw [rw_eq]; unfold h1; split_ifs <;> omega
include hP in
theorem bU : ∀ v, v < 3 → hU oP ((pfxVec a).extra) v < 2 + rowsWork NI := by
  intro v hv; unfold needP at hP; rw [rw_eq]; unfold hU; split_ifs <;> omega
omit hT hP in
theorem bC : ∀ v, v < 62 → hC NI v < 2 + rowsWork NI := by
  intro v hv; rw [rw_eq]; unfold hC; split_ifs <;> omega

include hT hP in
theorem g1_h1 (u : ℕ) (hu : u < 1 + 4 + (pfxVec a).extra + 1) : g1 NI oP (h1 NI oP u) = u := by
  unfold needP at hP
  unfold h1
  by_cases u0 : u = 0
  · rw [if_pos u0, u0]; rfl
  rw [if_neg u0]
  by_cases u1 : u = 1
  · rw [if_pos u1, u1]; unfold g1; rw [if_neg (by omega), if_pos rfl]
  rw [if_neg u1]
  by_cases u4 : u ≤ 4
  · rw [if_pos u4]; unfold g1; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
  · rw [if_neg u4]; unfold g1; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega

include hT hP in
theorem gC_hC (u : ℕ) (hu : u < 62) : gC NI (hC NI u) = u := by
  unfold needP at hP
  unfold hC
  by_cases u0 : u = 0
  · subst u0; rw [if_pos rfl]; unfold gC; rw [if_pos rfl]
  rw [if_neg u0]
  by_cases u30 : u = 30
  · subst u30; rw [if_pos rfl]; unfold gC; rw [if_neg (by omega), if_pos rfl]
  rw [if_neg u30]
  by_cases u60 : u = 60
  · subst u60; rw [if_pos rfl]; unfold gC; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [if_neg u60]
  by_cases u49 : u = 49
  · subst u49; rw [if_pos rfl]; unfold gC; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [if_neg u49]
  by_cases u10 : u = 10
  · subst u10; rw [if_pos rfl]; unfold gC
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [if_neg u10]
  by_cases u59 : u = 59
  · subst u59; rw [if_pos rfl]; unfold gC
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [if_neg u59]
  by_cases u43 : u = 43
  · subst u43; rw [if_pos rfl]; unfold gC
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl]
  rw [if_neg u43]
  by_cases u45 : u = 45
  · subst u45; rw [if_pos rfl]; unfold gC
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [if_neg u45]
  unfold gC
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

include hT hP in
theorem i1 : Function.Injective (s1 a NI oP) := vmap_inj (b1 a NI oP hP) (by
  intro v w hv hw h
  have := congrArg (g1 NI oP) h
  rwa [g1_h1 a NI oP hT hP v hv, g1_h1 a NI oP hT hP w hw] at this)
include hT hP in
theorem iU : Function.Injective (sU a NI oP) := vmap_inj (bU a NI oP hP) (by
  intro v w hv hw h; unfold needP at hP; unfold hU at h; split_ifs at h <;> omega)
include hT hP in
theorem iC : Function.Injective (sC NI) := vmap_inj (bC NI) (by
  intro v w hv hw h
  have := congrArg (gC NI) h
  rwa [gC_hC a NI oP hT hP v hv, gC_hC a NI oP hT hP w hw] at this)

end Maps

/-! ## 3. The machine, the chained banks, the run -/

theorem rcp_val (NI : ℕ) (i : Fin 64) : (rcpPort NI i).val = 2 + NI + 8 + i.val := by
  simp [rcpPort, fixPort] <;> omega

def machine (a : DecompositionAlgorithm) (NI oP : ℕ) :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine (s1 a NI oP) (MaskedReset.machine (pfxVec a).machine (fun _ => true)))
    (RecoveryFocus.machine (sU a NI oP) Streaming.machine)) (RecoveryFocus.machine (sC NI) RowsInit.capsMachine)

def cost (a : DecompositionAlgorithm) (r : Request) (w deg C hF cC dR rR : ℕ) : ℕ :=
  ((2 * (pfxVec a).cost r + 2) + 1 + (4 * (RowsInit.metaWord w deg C hF cC dR rR).length + 2)) + 1 +
    RowsInit.capsCost w deg C hF cC dR

/-- The unwrap's exit words. -/
def unOut (m : List Bool) : Fin 3 → List Bool := ![frame m, m, List.replicate m.length false]

section Banks
variable (a : DecompositionAlgorithm) (NI oP : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
  (B : Fin (1 + 4 + (pfxVec a).extra + 1) → List Bool) (m : List Bool) (Bc : Fin 62 → List Bool)

def bk1 := install (s1 a NI oP) A B
def bk2 := install (sU a NI oP) (bk1 a NI oP A B) (unOut m)
def bk3 := install (sC NI) (bk2 a NI oP A B m) Bc

variable (hT : 150 ≤ oP) (hP : oP + needP a ≤ NI)
include hT hP

omit hT in
theorem bk1_off (x : Fin (2 + rowsWork NI)) (h : ∀ v, v < 1 + 4 + (pfxVec a).extra + 1 → h1 NI oP v ≠ x.val) :
    bk1 a NI oP A B x = A x := inst_off (b1 a NI oP hP) A B x h
theorem bk2_off (x : Fin (2 + rowsWork NI)) (h1' : x.val ≠ 1) (h2' : x.val ≠ 151)
    (h3' : x.val ≠ 2 + oP + (pfxVec a).extra + 1) : bk2 a NI oP A B m x = bk1 a NI oP A B x :=
  inst_off (bU a NI oP hP) _ _ x (fun v hv h => by unfold hU at h; split_ifs at h <;> omega)
omit hT hP in
theorem bk3_off (x : Fin (2 + rowsWork NI)) (h : ∀ v, v < 62 → hC NI v ≠ x.val) :
    bk3 a NI oP A B m Bc x = bk2 a NI oP A B m x := inst_off (bC NI) _ Bc x h
theorem bk3_at (v : ℕ) (hv : v < 62) (x : Fin (2 + rowsWork NI)) (hx : x.val = hC NI v) :
    bk3 a NI oP A B m Bc x = Bc ⟨v, hv⟩ := inst_at (bC NI) (iC a NI oP hT hP) _ Bc x v hv hx
theorem bk1_at (v : ℕ) (hv : v < 1 + 4 + (pfxVec a).extra + 1) (x : Fin (2 + rowsWork NI)) (hx : x.val = h1 NI oP v) :
    bk1 a NI oP A B x = B ⟨v, hv⟩ := inst_at (b1 a NI oP hP) (i1 a NI oP hT hP) A B x v hv hx

/-- `hC` never hits the flags, `rowp 2`, `pub`. -/
theorem hC_ne (v : ℕ) (x : ℕ) (hv : v < 62) (hx : x < 2 + NI ∧ x ≠ 151 ∨ x = 2 + NI + 2) : hC NI v ≠ x := by
  unfold needP at hP; unfold hC; split_ifs <;> omega

end Banks

section Chain
variable (a : DecompositionAlgorithm) (NI oP : ℕ) (hT : 150 ≤ oP) (hP : oP + needP a ≤ NI)
include hT hP

/-- The three stages, from the entry bank. -/
theorem chain (r : Request) (w deg C hF cC dR rR : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (r.input a))
    (h1m : A (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR))
    (hRp : ∀ i : Fin 8, A (rowpPort NI i) = []) (hRc : ∀ i : Fin 64, A (rcpPort NI i) = [])
    (hI : ∀ x : Fin (2 + rowsWork NI), 148 ≤ x.val → x.val < 152 → A x = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oP ≤ x.val → x.val < 2 + oP + needP a → A x = []) :
    ∃ B Bc, Step (machine a NI oP) (cost a r w deg C hF cC dR rR) (fun _ => 0) A (fun _ => 0)
        (bk3 a NI oP A B (RowsInit.metaWord w deg C hF cC dR rR) Bc) ∧
      B ⟨0, by omega⟩ = frame (r.input a) ∧ (∀ j : Fin 4, B ⟨j.val + 1, by omega⟩ = pfxWord a j r) ∧
      Bc 10 = List.replicate C true ∧ Bc 30 = List.replicate cC true ∧ Bc 40 = List.replicate dR true ∧
      Bc 43 = List.replicate (hF + hF) true ∧ Bc 45 = List.replicate (hF + hF + 1) false ∧
      Bc 49 = List.replicate (cC + (cC + cC) + 2) false ∧ Bc 59 = List.replicate (RowsInit.ctrLen cC) false ∧
      Bc 60 = List.replicate (cC + 1) false := by
  have hn := hP
  unfold needP at hn hS
  have hb1 := b1 a NI oP hP
  have hbU := bU a NI oP hP
  have hbC := bC NI
  have ii1 := i1 a NI oP hT hP
  have iiU := iU a NI oP hT hP
  have iiC := iC a NI oP hT hP
  obtain ⟨B, s1r, b0, bj⟩ := vec_dock (pfxVec a) r (s1 a NI oP) ii1 (fun _ => 0) A (fun _ => rfl)
    (by rw [show s1 a NI oP ⟨0, by omega⟩ = pubPort NI 0 from Fin.ext (by rw [s1, vmap_val hb1]; rfl), h0])
    (by
      intro j hj
      have hv : (s1 a NI oP j).val = h1 NI oP j.val := vmap_val hb1 j
      have hl := j.isLt
      unfold h1 at hv
      rw [if_neg hj] at hv
      by_cases e1 : j.val = 1
      · rw [if_pos e1] at hv
        rw [show s1 a NI oP j = rowpPort NI 2 from Fin.ext (by rw [hv, rowpPort_val]; rfl)]
        exact hRp 2
      rw [if_neg e1] at hv
      by_cases e4 : j.val ≤ 4
      · rw [if_pos e4] at hv; exact hI _ (by omega) (by omega)
      · rw [if_neg e4] at hv; exact hS _ (by omega) (by omega))
  have key : ∀ j : Fin 4, B ⟨j.val + 1, by omega⟩ = pfxWord a j r := by
    intro j; fin_cases j <;> exact bj _ (by omega)
  obtain ⟨ru, hru, htu, hhu, -⟩ := UInputFields.unwrap_ready (RowsInit.metaWord w deg C hF cC dR rR)
  have su0 : Step Streaming.machine (4 * (RowsInit.metaWord w deg C hF cC dR rR).length + 2) (fun _ => 0)
      ![frame (RowsInit.metaWord w deg C hF cC dR rR), [], []] (fun _ => 0)
      (unOut (RowsInit.metaWord w deg C hF cC dR rR)) := Step.of_run hru (funext hhu) htu
  have sUr := run_dock su0 (sU a NI oP) iiU (fun _ => 0) (bk1 a NI oP A B) (fun _ => rfl) (by
    intro j
    fin_cases j
    · show bk1 a NI oP A B (sU a NI oP 0) = _
      have e : (sU a NI oP 0).val = 1 := by rw [sU, vmap_val hbU]; rfl
      rw [bk1_off a NI oP A B hP _ (fun v hv h => by rw [e] at h; unfold h1 at h; split_ifs at h <;> omega),
        show sU a NI oP 0 = pubPort NI 1 from Fin.ext e, h1m]; rfl
    · show bk1 a NI oP A B (sU a NI oP 1) = _
      have e : (sU a NI oP 1).val = 151 := by rw [sU, vmap_val hbU]; rfl
      rw [bk1_off a NI oP A B hP _ (fun v hv h => by rw [e] at h; unfold h1 at h; split_ifs at h <;> omega)]
      exact hI _ (by omega) (by omega)
    · show bk1 a NI oP A B (sU a NI oP 2) = _
      have e : (sU a NI oP 2).val = 2 + oP + (pfxVec a).extra + 1 := by rw [sU, vmap_val hbU]; rfl
      rw [bk1_off a NI oP A B hP _ (fun v hv h => by rw [e] at h; unfold h1 at h; split_ifs at h <;> omega)]
      exact hS _ (by omega) (by omega))
  obtain ⟨Bc, sCr, c10, c30, c40, c43, c45, c49, c59, c60⟩ := RowsInit.caps_dock (sC NI) iiC w deg C hF cC dR rR
    (fun _ => 0) (bk2 a NI oP A B (RowsInit.metaWord w deg C hF cC dR rR)) (fun _ => rfl)
    (by
      have e : sC NI 0 = sU a NI oP 1 := Fin.ext (by rw [sC, sU, vmap_val hbC, vmap_val hbU]; rfl)
      rw [e, bk2, install_slot _ iiU]; rfl)
    (by
      intro i hi
      have hv : (sC NI i).val = hC NI i.val := vmap_val hbC i
      have hl := i.isLt
      have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have hge : 2 + NI ≤ (sC NI i).val ∧ (sC NI i).val < 2 + NI + 72 := by
        rw [hv]; unfold hC; split_ifs <;> omega
      have hne2 : (sC NI i).val ≠ 2 + NI + 2 := by
        rw [hv]; exact hC_ne a NI oP hT hP i.val _ hl (Or.inr rfl)
      rw [bk2_off a NI oP A B _ hT hP _ (by omega) (by omega) (by omega),
        bk1_off a NI oP A B hP _ (fun v hv' h => by unfold h1 at h; split_ifs at h <;> omega)]
      by_cases hr : (sC NI i).val < 2 + NI + 8
      · have e : sC NI i = rowpPort NI ⟨(sC NI i).val - (2 + NI), by omega⟩ :=
          Fin.ext (by rw [rowpPort_val]; simp only; omega)
        rw [e]; exact hRp _
      · have e : sC NI i = rcpPort NI ⟨(sC NI i).val - (2 + NI + 8), by omega⟩ :=
          Fin.ext (by rw [rcp_val]; simp only; omega)
        rw [e]; exact hRc _)
  exact ⟨B, Bc, ((s1r.seq sUr).seq sCr).congr rfl rfl, b0, key, c10, c30, c40, c43, c45, c49, c59, c60⟩

end Chain

section Run
variable (a : DecompositionAlgorithm) (NI oP : ℕ) (hT : 150 ≤ oP) (hP : oP + needP a ≤ NI)
include hT hP

/-- `rowp` at the chained bank. -/
theorem rowp_out (r : Request) (C cC hF : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (B : Fin (1 + 4 + (pfxVec a).extra + 1) → List Bool) (m : List Bool) (Bc : Fin 62 → List Bool)
    (bk : ∀ j : Fin 4, B ⟨j.val + 1, by omega⟩ = pfxWord a j r)
    (c10 : Bc 10 = List.replicate C true) (c30 : Bc 30 = List.replicate cC true)
    (c43 : Bc 43 = List.replicate (hF + hF) true) (c45 : Bc 45 = List.replicate (hF + hF + 1) false)
    (c49 : Bc 49 = List.replicate (cC + (cC + cC) + 2) false) (c59 : Bc 59 = List.replicate (RowsInit.ctrLen cC) false)
    (c60 : Bc 60 = List.replicate (cC + 1) false) (i : Fin 8) :
    bk3 a NI oP A B m Bc (rowpPort NI i) = rowpWords (arityOf a r) C cC hF i := by
  have hn := hP
  unfold needP at hn
  obtain ⟨k, hk⟩ := i
  have hv : (rowpPort NI ⟨k, hk⟩).val = 2 + NI + k := by rw [rowpPort_val]
  have at' := bk3_at a NI oP A B m Bc hT hP
  interval_cases k
  · exact (at' 30 (by omega) _ (by rw [hv]; unfold hC; simp)).trans c30
  · exact (at' 60 (by omega) _ (by rw [hv]; unfold hC; simp)).trans c60
  · rw [bk3_off a NI oP A B m Bc _ (fun v hv' => hC_ne a NI oP hT hP v _ hv' (Or.inr (by rw [hv]))),
      bk2_off a NI oP A B m hT hP _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega),
      bk1_at a NI oP A B hT hP 1 (by omega) _ (by rw [hv]; rfl)]
    refine (bk 0).trans ?_
    show UnaryTemplate.tape (arityOf a r + 2) = UnaryTemplate.tape (2 * ((arityOf a r + 1) / 2) -
      (decide (arityOf a r % 2 = 1)).toNat + 2)
    rw [RowsInit.tpl_arith]
  · refine (at' 49 (by omega) _ (by rw [hv]; unfold hC; simp)).trans (c49.trans ?_)
    show List.replicate (cC + (cC + cC) + 2) false = List.replicate (3 * cC + 2) false
    congr 1; omega
  · exact (at' 10 (by omega) _ (by rw [hv]; unfold hC; simp)).trans c10
  · refine (at' 59 (by omega) _ (by rw [hv]; unfold hC; simp)).trans (c59.trans ?_)
    rw [RowsInit.ctrLen_eq]; rfl
  · refine (at' 43 (by omega) _ (by rw [hv]; unfold hC; simp)).trans (c43.trans ?_)
    show List.replicate (hF + hF) true = List.replicate (2 * hF) true
    congr 1; omega
  · refine (at' 45 (by omega) _ (by rw [hv]; unfold hC; simp)).trans (c45.trans ?_)
    show List.replicate (hF + hF + 1) false = List.replicate (2 * hF + 1) false
    congr 1; omega

/-- The three flags at the chained bank. -/
theorem flag_out (r : Request) (A : Fin (2 + rowsWork NI) → List Bool)
    (B : Fin (1 + 4 + (pfxVec a).extra + 1) → List Bool) (m : List Bool) (Bc : Fin 62 → List Bool)
    (bk : ∀ j : Fin 4, B ⟨j.val + 1, by omega⟩ = pfxWord a j r) (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    bk3 a NI oP A B m Bc (wp NI (147 + j)) = pfxWord a ⟨j, by omega⟩ r := by
  have hn := hP
  unfold needP at hn
  have hw : 147 + j < 2 + rowsWork NI := by rw [rw_eq]; omega
  have hf : (wp NI (147 + j)).val = h1 NI oP (j + 1) := by
    rw [wp_val hw]
    unfold h1
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    omega
  rw [bk3_off a NI oP A B m Bc _ (fun v hv' => hC_ne a NI oP hT hP v _ hv' (Or.inl (by rw [wp_val hw]; omega))),
    bk2_off a NI oP A B m hT hP _ (by rw [wp_val hw]; omega) (by rw [wp_val hw]; omega) (by rw [wp_val hw]; omega),
    bk1_at a NI oP A B hT hP (j + 1) (by omega) _ hf]
  exact bk ⟨j, by omega⟩

/-- The frame clause at the chained bank. -/
theorem frame_out (r : Request) (w deg C hF cC dR rR : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (r.input a))
    (h1m : A (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR))
    (B : Fin (1 + 4 + (pfxVec a).extra + 1) → List Bool) (Bc : Fin 62 → List Bool)
    (b0 : B ⟨0, by omega⟩ = frame (r.input a)) (x : Fin (2 + rowsWork NI))
    (hx1 : ¬ (2 + NI ≤ x.val ∧ x.val < 2 + NI + 72)) (hx2 : ¬ (148 ≤ x.val ∧ x.val < 152))
    (hx3 : ¬ (2 + oP ≤ x.val ∧ x.val < 2 + oP + needP a)) :
    bk3 a NI oP A B (RowsInit.metaWord w deg C hF cC dR rR) Bc x = A x := by
  have hn := hP
  unfold needP at hn hx3
  rw [bk3_off a NI oP A B _ Bc _ (fun v hv' h => by unfold hC at h; split_ifs at h <;> omega)]
  by_cases hx1' : x.val = 1
  · have hbU := bU a NI oP hP
    have ex : x = sU a NI oP 0 := Fin.ext (by rw [sU, vmap_val hbU, hx1']; rfl)
    rw [ex, bk2, install_slot _ (iU a NI oP hT hP)]
    show frame (RowsInit.metaWord w deg C hF cC dR rR) = A (sU a NI oP 0)
    rw [← ex, show x = pubPort NI 1 from Fin.ext hx1', h1m]
  rw [bk2_off a NI oP A B _ hT hP _ hx1' (by omega) (by omega)]
  by_cases hx0 : x.val = 0
  · rw [bk1_at a NI oP A B hT hP 0 (by omega) _ (by rw [hx0]; rfl), b0, show x = pubPort NI 0 from Fin.ext hx0, h0]
  · exact bk1_off a NI oP A B hP _ (fun v hv h => by unfold h1 at h; split_ifs at h <;> omega)

/-- **The work-phase prefix.** Entry: `pub 0` = framed request, `pub 1` = the framed metadata word, `rowp`, `rcp`,
`init 146–149` and the scratch blank; heads `0`. Exit: `rowp i = rowpWords (arityOf a r) C cC hF i`, `rcp 40 = 1^dR`,
`init 146 = 1^thrFlag`, `init 147 = 1^symFlag`, `init 148 = 1^|rows|` (ports 148–150); nothing outside `rowp`, `rcp`,
`init 146–149` and the scratch changes. -/
theorem run (r : Request) (w deg C hF cC dR rR : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (r.input a))
    (h1m : A (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR))
    (hRp : ∀ i : Fin 8, A (rowpPort NI i) = []) (hRc : ∀ i : Fin 64, A (rcpPort NI i) = [])
    (hI : ∀ x : Fin (2 + rowsWork NI), 148 ≤ x.val → x.val < 152 → A x = [])
    (hS : ∀ x : Fin (2 + rowsWork NI), 2 + oP ≤ x.val → x.val < 2 + oP + needP a → A x = []) :
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine a NI oP) (cost a r w deg C hF cC dR rR) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ i : Fin 8, A' (rowpPort NI i) = rowpWords (arityOf a r) C cC hF i) ∧
      A' (rcpPort NI 40) = List.replicate dR true ∧
      A' (wp NI 148) = List.replicate (thrFlag r) true ∧
      A' (wp NI 149) = List.replicate (symFlag r) true ∧
      A' (wp NI 150) = List.replicate (r.family a).rows.length true ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 + NI ≤ x.val ∧ x.val < 2 + NI + 72) → ¬ (148 ≤ x.val ∧ x.val < 152) →
        ¬ (2 + oP ≤ x.val ∧ x.val < 2 + oP + needP a) → A' x = A x) := by
  obtain ⟨B, Bc, hs, b0, bk, c10, c30, c40, c43, c45, c49, c59, c60⟩ :=
    chain a NI oP hT hP r w deg C hF cC dR rR A h0 h1m hRp hRc hI hS
  have hn := hP
  unfold needP at hn
  refine ⟨_, hs, rowp_out a NI oP hT hP r C cC hF A B _ Bc bk c10 c30 c43 c45 c49 c59 c60, ?_,
    flag_out a NI oP hT hP r A B _ Bc bk 1 (by omega) (by omega),
    flag_out a NI oP hT hP r A B _ Bc bk 2 (by omega) (by omega),
    flag_out a NI oP hT hP r A B _ Bc bk 3 (by omega) (by omega),
    frame_out a NI oP hT hP r w deg C hF cC dR rR A h0 h1m B Bc b0⟩
  exact (bk3_at a NI oP A B _ Bc hT hP 40 (by omega) _ (by rw [rcp_val]; unfold hC; simp)).trans c40

end Run

end
end RowsInit.Prefix
