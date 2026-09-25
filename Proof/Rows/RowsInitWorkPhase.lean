import Proof.Rows.RowsInitThrWork

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.WorkPhase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta
open RowsInit.ThrLoop (wp wp_val rw_eq)
open RowsInit.ThrWork (port_cases stop_run cell0_rep)
noncomputable section

/-- The work phase's entry bank: the framed request on `pub 0`, the framed metadata word on `pub 1`, all else blank. -/
def workIn (NI : ℕ) (x m : List Bool) : Fin (2 + rowsWork NI) → List Bool :=
  fun k => if k.val = 0 then x else if k.val = 1 then m else []

/-- **The SYM branch, typed** (exactly `ThrWork.branch_ne` / `branch_e` at SYM; regions from `oB`). -/
structure SymSpec (a : DecompositionAlgorithm) (NI oB : ℕ) (h : 146 ≤ NI) where
  states : ℕ
  machine : Machine (2 + rowsWork NI) states
  costNe : Request → ℕ
  costE : Request → ℕ
  run_ne : ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target C cC hF : ℕ)
    (A : Fin (2 + rowsWork NI) → List Bool),
    A (pubPort NI 0) = frame (Request.input a (.sym r four L target)) →
    (∀ i, A (rowpPort NI i) = rowpWords (symN r L target) C cC hF i) →
    (∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A x = []) →
    A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length true →
    (∀ x : Fin (2 + rowsWork NI), 2 + oB ≤ x.val → x.val < 2 + NI → A x = []) →
    (∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = []) →
    0 < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length →
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step machine (costNe (.sym r four L target)) (fun _ => 0) A (fun _ => 0) B ∧
      B = symBase a r four L target NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i))
        (fun i => B (rcpPort NI i)) C cC hF 0 ∧
      PartsStep.SymC5Ready a r four L target NI (fun i => B (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.iniS NI h) ∧
      (∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 ≤ x.val ∧ x.val < 148) →
        ¬ (2 + oB ≤ x.val ∧ x.val < 2 + NI) → B x = A x)
  run_e : ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target C cC hF : ℕ)
    (A : Fin (2 + rowsWork NI) → List Bool),
    (∀ i, A (rowpPort NI i) = rowpWords (symN r L target) C cC hF i) →
    A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length true →
    (∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = []) →
    (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length = 0 →
    Step machine (costE (.sym r four L target)) (fun _ => 0) A (fun _ => 0) A ∧
      A = symBase a r four L target NI (fun i => A (pubPort NI i)) (fun i => A (initPort NI i))
        (fun i => A (rcpPort NI i)) C cC hF 0

/-! ## 1. The machine -/

section Machine
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (NI oP oT o oC : ℕ) (h : 146 ≤ NI) (S : SymSpec a NI oT h)

/-- The branch part: THR flag (port 148) → THR branch; else SYM flag (port 149) → SYM branch; else stop. -/
def branchesM := CloseoutRowsOriginalSwitch.machine (RowsInit.ThrWork.branchM a bnd bndW NI oT o oC h)
  (CloseoutRowsOriginalSwitch.machine S.machine (CloseoutRowsOriginalSwitch.stop (2 + rowsWork NI)) (wp NI 149)) (wp NI 148)

/-- **The work phase** (one fixed machine). -/
def workM := Composition.machine (RowsInit.Prefix.machine a NI oP) (branchesM a bnd bndW NI oT o oC h S)

end Machine

/-! ## 2. After the prefix -/

section Pre
variable (a : DecompositionAlgorithm) (NI oP oT : ℕ) (hT : 150 ≤ oP) (hP : oP + RowsInit.Prefix.needP a ≤ oT)
  (hNI : oT ≤ NI)
include hT hP hNI

/-- The prefix from the work phase's entry bank, with every fact the branches read. -/
theorem pre (r : Request) (w deg C hF cC dR rR : ℕ) :
    ∃ A1 : Fin (2 + rowsWork NI) → List Bool,
      Step (RowsInit.Prefix.machine a NI oP) (RowsInit.Prefix.cost a r w deg C hF cC dR rR) (fun _ => 0)
        (workIn NI (frame (r.input a)) (frame (RowsInit.metaWord w deg C hF cC dR rR))) (fun _ => 0) A1 ∧
      A1 (pubPort NI 0) = frame (r.input a) ∧
      A1 (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR) ∧
      (∀ i, A1 (rowpPort NI i) = rowpWords (RowsInit.Prefix.arityOf a r) C cC hF i) ∧
      A1 (rcpPort NI 40) = List.replicate dR true ∧
      A1 (wp NI 148) = List.replicate (thrFlag r) true ∧
      A1 (wp NI 149) = List.replicate (RowsInit.Prefix.symFlag r) true ∧
      A1 (wp NI 150) = List.replicate (r.family a).rows.length true ∧
      (∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A1 x = []) ∧
      (∀ x : Fin (2 + rowsWork NI), 2 + oP + RowsInit.Prefix.needP a ≤ x.val → x.val < 2 + NI → A1 x = []) ∧
      (∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A1 x = []) := by
  have hPN : oP + RowsInit.Prefix.needP a ≤ NI := by omega
  have blank : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val →
      workIn NI (frame (r.input a)) (frame (RowsInit.metaWord w deg C hF cC dR rR)) x = [] := by
    intro x hx; simp only [workIn]; rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨A1, s1, hR, h40, h148, h149, h150, hF1⟩ := RowsInit.Prefix.run a NI oP hT hPN r w deg C hF cC dR rR _ rfl rfl
    (fun i => blank _ (by rw [rowpPort_val]; omega)) (fun i => blank _ (by rw [RowsInit.Prefix.rcp_val]; omega))
    (fun x h1 _ => blank x (by omega)) (fun x h1 _ => blank x (by omega))
  have p0 : (pubPort NI 0).val = 0 := rfl
  have p1 : (pubPort NI 1).val = 1 := rfl
  exact ⟨A1, s1, by rw [hF1 _ (by rw [p0]; omega) (by rw [p0]; omega) (by rw [p0]; omega)]; rfl,
    by rw [hF1 _ (by rw [p1]; omega) (by rw [p1]; omega) (by rw [p1]; omega)]; rfl,
    hR, h40, h148, h149, h150,
    fun x h1 h2 => by rw [hF1 x (by omega) (by omega) (by omega)]; exact blank x h1,
    fun x h1 h2 => by rw [hF1 x (by omega) (by omega) (by omega)]; exact blank x (by omega),
    fun x h1 => by rw [hF1 x (by omega) (by omega) (by omega)]; exact blank x (by omega)⟩

end Pre

/-! ## 3. The five cases -/

section Cases
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → WordStage a (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (NI oP oT o oC : ℕ) (h : 146 ≤ NI) (S : SymSpec a NI oT h)
  (hT : 150 ≤ oP) (hP : oP + RowsInit.Prefix.needP a ≤ oT)
  (hTo : oT + RowsInit.ThrInitRun.need a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU ≤ o)
  (hNo : o + RowsInit.ThrLoop.need a ≤ oC) (hC : oC + RowsInit.C5.needC a ≤ NI)
  (w deg C hF cC dR rR : ℕ)
include hT hP hTo hNo hC

def Side (r : Request) (B : Fin (2 + rowsWork NI) → List Bool) : Prop :=
  B (pubPort NI 0) = frame (r.input a) ∧ B (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR) ∧
  B (rcpPort NI 40) = List.replicate dR true ∧ B (wp NI 150) = List.replicate (r.family a).rows.length true ∧
  (∀ x : Fin (2 + rowsWork NI), 2 + oP + RowsInit.Prefix.needP a ≤ x.val → x.val < 2 + oT → B x = [])

omit hTo hNo hC in
theorem side_of (r : Request) (A1 B : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A1 (pubPort NI 0) = frame (r.input a))
    (h1 : A1 (pubPort NI 1) = frame (RowsInit.metaWord w deg C hF cC dR rR))
    (h40 : A1 (rcpPort NI 40) = List.replicate dR true)
    (h150 : A1 (wp NI 150) = List.replicate (r.family a).rows.length true)
    (hbl : ∀ x : Fin (2 + rowsWork NI), 2 + oP + RowsInit.Prefix.needP a ≤ x.val → x.val < 2 + NI → A1 x = [])
    (hNI : oT ≤ NI)
    (hf : ∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 ≤ x.val ∧ x.val < 148) →
      ¬ (2 + oT ≤ x.val ∧ x.val < 2 + NI) → B x = A1 x) :
    Side a NI oP oT w deg C hF cC dR rR r B := by
  have p0 : (pubPort NI 0).val = 0 := rfl
  have p1 : (pubPort NI 1).val = 1 := rfl
  have hw : 150 < 2 + rowsWork NI := by rw [rw_eq]; omega
  refine ⟨?_, ?_, ?_, ?_, fun x h1' h2' => ?_⟩
  · rw [hf _ (by rw [p0]; omega) (by rw [p0]; omega) (by rw [p0]; omega)]; exact h0
  · rw [hf _ (by rw [p1]; omega) (by rw [p1]; omega) (by rw [p1]; omega)]; exact h1
  · have := RowsInit.Prefix.rcp_val NI 40
    rw [hf _ (by omega) (by omega) (by omega)]; exact h40
  · rw [hf _ (by rw [wp_val hw]; omega) (by rw [wp_val hw]; omega) (by rw [wp_val hw]; omega)]; exact h150
  · rw [hf _ (by omega) (by omega) (by omega)]; exact hbl x h1' (by omega)

/-- **THR, nonempty family.** -/
theorem thr_ne (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (hN : RowsInit.Prefix.arityOf a (.thr r four L target) = thrN a r L target)
    (hbnd : ∀ c, bnd (.thr r four L target) c = ThrSel.bnd a r c)
    (hne : 0 < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length) :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (workM a bnd bndW NI oP oT o oC h S)
        (RowsInit.Prefix.cost a (.thr r four L target) w deg C hF cC dR rR + 1 +
          (RowsInit.ThrWork.neCost a bnd bndW r four L target + 2 + 2)) (fun _ => 0)
        (workIn NI (frame (Request.input a (.thr r four L target))) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i)) (fun i => B (rcpPort NI i)) C cC hF
        (.thr r four L target) 0 ∧
      PartsStep.ThrC5Ready a r four L target NI (fun i => B (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.ini NI h) (ThrInitReady.ix NI h) (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h)
        (PrimeReserve.rpOf a (.thr r four L target)) ∧
      Side a NI oP oT w deg C hF cC dR rR (.thr r four L target) B := by
  have hNI : oT ≤ NI := by unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A1, s1, h0, h1, hR, h40, h148, -, h150, hF1, hbl, hB⟩ := pre a NI oP oT hT hP hNI (.thr r four L target)
    w deg C hF cC dR rR
  rw [hN] at hR
  obtain ⟨B, sb, eb, cb, fb⟩ := RowsInit.ThrWork.branch_ne a bnd bndW NI oT o oC h r four L target (by omega) hTo hNo hC
    C cC hF A1 h0 hR hF1 h150 (fun x h1' h2' => hbl x (by omega) h2') hB hbnd hne
  refine ⟨B, s1.seq (CloseoutRowsOriginalSwitch.true_run _ _ _ sb (by rw [h148]; rfl)), eb, cb,
    side_of a NI oP oT hT hP w deg C hF cC dR rR _ A1 B h0 h1 h40 h150 hbl hNI fb⟩

/-- **THR, empty family.** -/
theorem thr_e (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (hN : RowsInit.Prefix.arityOf a (.thr r four L target) = thrN a r L target)
    (he : (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length = 0) :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (workM a bnd bndW NI oP oT o oC h S)
        (RowsInit.Prefix.cost a (.thr r four L target) w deg C hF cC dR rR + 1 + (0 + 2 + 2)) (fun _ => 0)
        (workIn NI (frame (Request.input a (.thr r four L target))) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i)) (fun i => B (rcpPort NI i)) C cC hF
        (.thr r four L target) 0 ∧
      Side a NI oP oT w deg C hF cC dR rR (.thr r four L target) B := by
  have hNI : oT ≤ NI := by unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A1, s1, h0, h1, hR, h40, h148, -, h150, -, hbl, hB⟩ := pre a NI oP oT hT hP hNI (.thr r four L target)
    w deg C hF cC dR rR
  rw [hN] at hR
  obtain ⟨sb, eb⟩ := RowsInit.ThrWork.branch_e a bnd bndW NI oT o oC h r four L target C cC hF A1 hR h150 hB he
  refine ⟨A1, s1.seq (CloseoutRowsOriginalSwitch.true_run _ _ _ sb (by rw [h148]; rfl)), eb,
    side_of a NI oP oT hT hP w deg C hF cC dR rR _ A1 A1 h0 h1 h40 h150 hbl hNI (fun _ _ _ _ => rfl)⟩

/-- **SYM, nonempty family** (through the typed SYM branch). -/
theorem sym_ne (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (hN : RowsInit.Prefix.arityOf a (.sym r four L target) = symN r L target)
    (hne : 0 < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length) :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (workM a bnd bndW NI oP oT o oC h S)
        (RowsInit.Prefix.cost a (.sym r four L target) w deg C hF cC dR rR + 1 +
          (S.costNe (.sym r four L target) + 2 + 2)) (fun _ => 0)
        (workIn NI (frame (Request.input a (.sym r four L target))) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i)) (fun i => B (rcpPort NI i)) C cC hF
        (.sym r four L target) 0 ∧
      PartsStep.SymC5Ready a r four L target NI (fun i => B (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.iniS NI h) ∧
      Side a NI oP oT w deg C hF cC dR rR (.sym r four L target) B := by
  have hNI : oT ≤ NI := by unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A1, s1, h0, h1, hR, h40, h148, h149, h150, hF1, hbl, hB⟩ := pre a NI oP oT hT hP hNI (.sym r four L target)
    w deg C hF cC dR rR
  rw [hN] at hR
  obtain ⟨B, sb, eb, cb, fb⟩ := S.run_ne r four L target C cC hF A1 h0 hR hF1 h150
    (fun x h1' h2' => hbl x (by omega) h2') hB hne
  refine ⟨B, s1.seq (CloseoutRowsOriginalSwitch.false_run _ _ _
      (CloseoutRowsOriginalSwitch.true_run _ _ _ sb (by rw [h149]; rfl)) (by rw [h148]; rfl)), eb, cb,
    side_of a NI oP oT hT hP w deg C hF cC dR rR _ A1 B h0 h1 h40 h150 hbl hNI fb⟩

/-- **SYM, empty family.** -/
theorem sym_e (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (hN : RowsInit.Prefix.arityOf a (.sym r four L target) = symN r L target)
    (he : (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length = 0) :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (workM a bnd bndW NI oP oT o oC h S)
        (RowsInit.Prefix.cost a (.sym r four L target) w deg C hF cC dR rR + 1 +
          (S.costE (.sym r four L target) + 2 + 2)) (fun _ => 0)
        (workIn NI (frame (Request.input a (.sym r four L target))) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i)) (fun i => B (rcpPort NI i)) C cC hF
        (.sym r four L target) 0 ∧
      Side a NI oP oT w deg C hF cC dR rR (.sym r four L target) B := by
  have hNI : oT ≤ NI := by unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A1, s1, h0, h1, hR, h40, h148, h149, h150, -, hbl, hB⟩ := pre a NI oP oT hT hP hNI (.sym r four L target)
    w deg C hF cC dR rR
  rw [hN] at hR
  obtain ⟨sb, eb⟩ := S.run_e r four L target C cC hF A1 hR h150 hB he
  refine ⟨A1, s1.seq (CloseoutRowsOriginalSwitch.false_run _ _ _
      (CloseoutRowsOriginalSwitch.true_run _ _ _ sb (by rw [h149]; rfl)) (by rw [h148]; rfl)), eb,
    side_of a NI oP oT hT hP w deg C hF cC dR rR _ A1 A1 h0 h1 h40 h150 hbl hNI (fun _ _ _ _ => rfl)⟩

/-- **The terminal sentinel** (empty family, `rowpWords 0`). -/
theorem term :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (workM a bnd bndW NI oP oT o oC h S)
        (RowsInit.Prefix.cost a .terminal w deg C hF cC dR rR + 1 + (0 + 2 + 2)) (fun _ => 0)
        (workIn NI (frame (Request.input a .terminal)) (frame (RowsInit.metaWord w deg C hF cC dR rR)))
        (fun _ => 0) B ∧
      B = baseOf a NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i)) (fun i => B (rcpPort NI i)) C cC hF
        .terminal 0 ∧
      Side a NI oP oT w deg C hF cC dR rR .terminal B := by
  have hNI : oT ≤ NI := by unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A1, s1, h0, h1, hR, h40, h148, h149, h150, -, hbl, hB⟩ := pre a NI oP oT hT hP hNI .terminal
    w deg C hF cC dR rR
  refine ⟨A1, s1.seq (CloseoutRowsOriginalSwitch.false_run _ _ _
      (CloseoutRowsOriginalSwitch.false_run _ _ _ (stop_run _ _) (by rw [h149]; rfl)) (by rw [h148]; rfl)), ?_,
    side_of a NI oP oT hT hP w deg C hF cC dR rR _ A1 A1 h0 h1 h40 h150 hbl hNI (fun _ _ _ _ => rfl)⟩
  have ha : RowsInit.Prefix.arityOf a .terminal = 0 := by simp [RowsInit.Prefix.arityOf, liveFlag]
  rw [ha] at hR
  funext p
  rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [baseOf, layout_pub]
  · simp only [baseOf, layout_init]
  · simp only [baseOf, layout_rowp]; exact hR i
  · simp only [baseOf, layout_rcp]
  · simp only [baseOf, layout_loop]; exact hB _ (by rw [RowsInit.ThrLoop.loop_val]; omega)
  · simp only [baseOf, layout_c6]; exact hB _ (by rw [RowsInit.ThrLoop.c6_val]; omega)
  · simp only [baseOf, layout_c5]; exact hB _ (by rw [RowsInit.C5.c5_val]; omega)

end Cases

end
end RowsInit.WorkPhase
