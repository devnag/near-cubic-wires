import Proof.Rows.RowsInitThrInitReady
import Proof.Rows.RowsInitPrefix

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.ThrWork
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.ThrLoop (wp wp_val rw_eq init_val loop_val c6_val)
noncomputable section

/-! ## 1. Every work port lies in one of the seven blocks -/

theorem port_cases (NI : ℕ) (p : Fin (2 + rowsWork NI)) :
    (∃ i, p = pubPort NI i) ∨ (∃ i, p = initPort NI i) ∨ (∃ i, p = rowpPort NI i) ∨ (∃ i, p = rcpPort NI i) ∨
      (∃ i, p = loopPort NI i) ∨ (∃ i, p = c6Port NI i) ∨ (∃ i, p = c5Port NI i) := by
  have hp : p.val < 2 + (NI + 610) := rw_eq NI ▸ p.isLt
  by_cases h1 : p.val < 2
  · exact Or.inl ⟨⟨p.val, h1⟩, Fin.ext rfl⟩
  by_cases h2 : p.val < 2 + NI
  · exact Or.inr (Or.inl ⟨⟨p.val - 2, by omega⟩, Fin.ext (by rw [init_val]; simp only; omega)⟩)
  by_cases h3 : p.val < 2 + NI + 8
  · exact Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI), by omega⟩, Fin.ext (by rw [rowpPort_val]; simp only; omega)⟩))
  by_cases h4 : p.val < 2 + NI + 72
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 8), by omega⟩,
      Fin.ext (by rw [RowsInit.Prefix.rcp_val]; simp only; omega)⟩)))
  by_cases h5 : p.val < 2 + NI + 592
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 72), by simp [MT]; omega⟩,
      Fin.ext (by rw [loop_val]; simp only; omega)⟩))))
  by_cases h6 : p.val < 2 + NI + 594
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p.val - (2 + NI + 592), by omega⟩,
      Fin.ext (by rw [c6_val]; simp only; omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨p.val - (2 + NI + 594), by omega⟩,
      Fin.ext (by rw [RowsInit.C5.c5_val]; simp only; omega)⟩)))))

/-! ## 2. The halting machine and the switch -/

theorem stop_run {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop t) 0 H A H A :=
  ⟨_, runFrom_zero_of_halted (CloseoutRowsOriginalSwitch.stop t) _ rfl, rfl, rfl, le_refl 0⟩

theorem cell0_rep (n : ℕ) : readTapeBit (List.replicate n true) 0 = decide (0 < n) := by
  cases n <;> rfl

/-! ## 3. The shape of `thrBase … 0` (with and without a first key) -/

section Shape
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target NI C cC hF : ℕ) (X : Fin (2 + rowsWork NI) → List Bool)

/-- A bank with row 0's blocks, the ten key masters blank, IS `thrBlank0` of `thrBase … 0` at its own `pub/init/rcp`. -/
theorem thr_shape (k0 : RCFive.RowKeys.ThrKey a r L target) (hk : thrKeyAt a r L target 0 = some k0)
    (hR : ∀ i, X (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hK : ∀ k ∈ thrKeySet, X (masterPort NI k) = [])
    (hL : ∀ i, (∀ k ∈ thrKeySet, loopPort NI i ≠ masterPort NI k) → X (loopPort NI i) =
      loopBank (thrLive r L) (thrRes r.q (ThrWidth.T a r four L target))
        (thrMasters a r four L target (thrRes r.q (ThrWidth.T a r four L target)) k0) i)
    (h6 : ∀ i, X (c6Port NI i) = c6Words (thrLive r L)ᶜ.card i)
    (h5 : ∀ i, X (c5Port NI i) = c5Words (seedWords (thrSeedIdx a r L target k0) (thrSeeds a r L target).length)
      (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
      (seedScratch (thrSeeds a r L target).length) i) :
    X = KeyZeroThr.thrBlank0 NI (thrBase a r four L target NI (fun i => X (pubPort NI i)) (fun i => X (initPort NI i))
      (fun i => X (rcpPort NI i)) C cC hF 0) := by
  funext p
  rw [KeyZeroMode.thrBlank0_eq]
  unfold KeyZeroMode.keyBlank
  split_ifs with hp
  · obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp hp
    exact hK k hk'
  · rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [thrBase, hk, layout_pub]
    · simp only [thrBase, hk, layout_init]
    · simp only [thrBase, hk, layout_rowp]; exact hR i
    · simp only [thrBase, hk, layout_rcp]
    · simp only [thrBase, hk, layout_loop]
      exact hL i (fun k hk' he => hp (Finset.mem_image.mpr ⟨k, hk', he.symm⟩))
    · simp only [thrBase, hk, layout_c6]; exact h6 i
    · simp only [thrBase, hk, layout_c5]; exact h5 i

/-- Without a first key (empty family), `thrBase … 0` has blank loop, C6 and C5 blocks. -/
theorem thr_shape_none (hk : thrKeyAt a r L target 0 = none)
    (hR : ∀ i, X (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → X x = []) :
    X = thrBase a r four L target NI (fun i => X (pubPort NI i)) (fun i => X (initPort NI i))
      (fun i => X (rcpPort NI i)) C cC hF 0 := by
  funext p
  rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [thrBase, hk, layout_pub]
  · simp only [thrBase, hk, layout_init]
  · simp only [thrBase, hk, layout_rowp]; exact hR i
  · simp only [thrBase, hk, layout_rcp]
  · simp only [thrBase, hk, layout_loop]; exact hB _ (by rw [loop_val]; omega)
  · simp only [thrBase, hk, layout_c6]; exact hB _ (by rw [c6_val]; omega)
  · simp only [thrBase, hk, layout_c5]; exact hB _ (by rw [RowsInit.C5.c5_val]; omega)

end Shape

/-! ## 4. The key-0 branch: loop block + C6, C5, RC5's key-0 writer -/

section Main
variable (a : DecompositionAlgorithm) (NI o oC : ℕ) (h : 146 ≤ NI)

/-- Loop block + C6 ; C5 (the part before the key-0 writer). -/
def preM := Composition.machine (RowsInit.ThrLoop.machine a NI o) (RowsInit.C5.machine a NI oC)

/-- **The key-0 branch.** -/
def mainM := Composition.machine (preM a NI o oC)
  (KeyZeroMode.k0 NI (ThrInitReady.iMode NI h) (ThrInitReady.iz NI h) (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h)
    (ThrInitReady.iniS NI h))

variable (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)

def preCost : ℕ := RowsInit.ThrLoop.cost a (.thr r four L target) + 1 + RowsInit.C5.cost a (.thr r four L target)

def mainCost : ℕ := preCost a r four L target + 1 +
  (KeyZeroThr.thrK0Cost (KeyTop.wT a r four L target) (ThrWidth.T a r four L target)
    (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target))
    (ThrSelBase.baseCost (ThrSelBase.bF (ThrWidth.T a r four L target)) (KeyTop.wT a r four L target)) + 2)

theorem key_head (hne : 0 < (RCFive.RowKeys.thrKeys a r L target).length) :
    ∃ k0, thrKeyAt a r L target 0 = some k0 := by
  refine ⟨(RCFive.RowKeys.thrKeys a r L target)[0], ?_⟩
  simp only [thrKeyAt, Nat.zero_mod, List.getElem?_eq_getElem hne]

/-- The loop block, C6 and C5 of row 0, the ten key masters blank: `thrBlank0` of `thrBase … 0`. -/
theorem pre_run (hNo : o + RowsInit.ThrLoop.need a ≤ oC) (hC : oC + RowsInit.C5.needC a ≤ NI)
    (C cC hF : ℕ) (A1 : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A1 (pubPort NI 0) = frame (Request.input a (.thr r four L target)))
    (hR : ∀ i, A1 (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + NI → A1 x = [])
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A1 x = [])
    (k0 : RCFive.RowKeys.ThrKey a r L target) (hk : thrKeyAt a r L target 0 = some k0) :
    ∃ A3 : Fin (2 + rowsWork NI) → List Bool,
      Step (preM a NI o oC) (preCost a r four L target) (fun _ => 0) A1 (fun _ => 0) A3 ∧
      A3 = KeyZeroThr.thrBlank0 NI (thrBase a r four L target NI (fun i => A3 (pubPort NI i))
        (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0) ∧
      (∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 + o ≤ x.val ∧ x.val < 2 + NI) → A3 x = A1 x) := by
  have hNI : o + RowsInit.ThrLoop.need a ≤ NI := by
    unfold RowsInit.C5.needC at hC; omega
  obtain ⟨A2, s2, hK2, hL2, h62, hF2⟩ := RowsInit.ThrLoop.loop_run a NI o hNI r four L target k0 A1 h0
    (fun x h1 h2 => hI x h1 (by omega)) (fun x h1 h2 => hB x h1)
  have e20 : A2 (pubPort NI 0) = frame (Request.input a (.thr r four L target)) := by
    rw [hF2 _ (by rw [RowsInit.ThrLoop.pub_val]; simp) (by rw [RowsInit.ThrLoop.pub_val]; simp), h0]
  have c5eq : ∀ i : Fin 16, A2 (c5Port NI i) = A1 (c5Port NI i) := fun i =>
    hF2 _ (by rw [RowsInit.C5.c5_val]; unfold RowsInit.ThrLoop.need at hNI; omega) (by rw [RowsInit.C5.c5_val]; omega)
  obtain ⟨A3, s3, h012, h7, h11, h12, hz3, hF3⟩ := RowsInit.C5.run a NI oC hC (.thr r four L target) A2 e20
    (fun i _ => by rw [c5eq]; exact hB _ (by rw [RowsInit.C5.c5_val]; omega))
    (fun x h1 h2 => by
      unfold RowsInit.C5.needC at h2 hC
      rw [hF2 _ (by omega) (by omega)]
      exact hI x (by omega) (by omega))
  have f32 : ∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 594 → ¬ (2 + oC ≤ x.val ∧ x.val < 2 + oC + RowsInit.C5.needC a) →
      A3 x = A2 x := fun x h1 h2 => hF3 x (by omega) h2
  refine ⟨A3, s2.seq s3, ?_, fun x hx1 hx2 => ?_⟩
  · refine thr_shape a r four L target NI C cC hF A3 k0 hk (fun i => ?_) (fun k hk' => ?_) (fun i hi => ?_)
      (fun i => ?_) (fun i => ?_)
    · have hv := rowpPort_val NI i
      have hi := i.isLt
      rw [f32 _ (by omega) (by omega), hF2 _ (by omega) (by omega)]
      exact hR i
    · have hv := RowsInit.ThrLoop.master_val NI k
      have hi := k.isLt
      rw [f32 _ (by omega) (by omega)]
      exact hK2 k hk'
    · have hv := loop_val NI i
      have hi' := i.isLt
      simp only [MT] at hi'
      rw [f32 _ (by omega) (by omega)]
      exact hL2 i hi
    · have hv := c6_val NI i
      have hi := i.isLt
      rw [f32 _ (by omega) (by omega)]
      exact h62 i
    · refine RowsInit.C5.thr_block a r four L target NI A3 k0 hk h012 h7 h11 h12 (fun i hi => ?_) i
      rw [hz3 i hi, c5eq]
      exact hB _ (by rw [RowsInit.C5.c5_val]; omega)
  · rw [hF3 x (by omega) (by omega), hF2 x (by omega) (by omega)]

end Main

section Main2
variable (a : DecompositionAlgorithm) (NI o oC : ℕ) (h : 146 ≤ NI)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)

/-- **The key-0 branch run**: from the bank after the THR init words (`WordsAt`), to `thrBase … 0` at its own blocks,
with `ThrC5Ready` on its `init` block. -/
theorem main_run (hNo : o + RowsInit.ThrLoop.need a ≤ oC) (hC : oC + RowsInit.C5.needC a ≤ NI) (ho : 146 ≤ o)
    (C cC hF : ℕ) (A1 : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A1 (pubPort NI 0) = frame (Request.input a (.thr r four L target)))
    (hR : ∀ i, A1 (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + NI → A1 x = [])
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A1 x = [])
    (bnd : Request → Fin 4 → ℕ) (oT : ℕ) (hT : 146 ≤ oT)
    (hW : ThrInitReady.WordsAt a bnd ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU NI oT
      (.thr r four L target) A1)
    (hbnd : ∀ c, bnd (.thr r four L target) c = ThrSel.bnd a r c)
    (hne : 0 < (RCFive.RowKeys.thrKeys a r L target).length) :
    ∃ A4 : Fin (2 + rowsWork NI) → List Bool,
      Step (mainM a NI o oC h) (mainCost a r four L target) (fun _ => 0) A1 (fun _ => 0) A4 ∧
      A4 = thrBase a r four L target NI (fun i => A4 (pubPort NI i)) (fun i => A4 (initPort NI i))
        (fun i => A4 (rcpPort NI i)) C cC hF 0 ∧
      PartsStep.ThrC5Ready a r four L target NI (fun i => A4 (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.ini NI h) (ThrInitReady.ix NI h) (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h)
        (PrimeReserve.rpOf a (.thr r four L target)) ∧
      (∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 + o ≤ x.val ∧ x.val < 2 + NI) → A4 x = A1 x) := by
  obtain ⟨k0, hk⟩ := key_head a r L target hne
  obtain ⟨A3, s3, e3, f3⟩ := pre_run a NI o oC r four L target hNo hC C cC hF A1 h0 hR hI hB k0 hk
  have hW3 := ThrInitReady.wordsAt_transport a bnd _ _ _ _ NI oT hT _ A1 A3 hW
    (fun x h1 h2 => f3 x (by omega) (by omega))
  have c5r := ThrInitReady.thr_c5 a bnd NI oT h r four L target A3 hW3 hbnd
  obtain ⟨hmode, -, -, hib, hone, -, hinitB, hinitO⟩ := c5r
  have sk := KeyZeroMode.thr_k0 a r four L target NI (fun i => A3 (pubPort NI i)) (fun i => A3 (initPort NI i))
    (fun i => A3 (rcpPort NI i)) C cC hF (ThrInitReady.iMode NI h) hmode (ThrInitReady.iz NI h)
    (ThrInitReady.iz_inj NI h) (ThrInitReady.thr_iz a bnd NI oT h r four L target A3 hW3) (ThrInitReady.ib NI h)
    (ThrInitReady.iOne NI h) hib hone hinitB hinitO (ThrInitReady.iniS NI h) hne
  have sk' := (congrArg (fun B => Step (KeyZeroMode.k0 NI (ThrInitReady.iMode NI h) (ThrInitReady.iz NI h)
      (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h) (ThrInitReady.iniS NI h))
      (KeyZeroThr.thrK0Cost (KeyTop.wT a r four L target) (ThrWidth.T a r four L target)
        (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target))
        (ThrSelBase.baseCost (ThrSelBase.bF (ThrWidth.T a r four L target)) (KeyTop.wT a r four L target)) + 2)
      (fun _ => 0) B (fun _ => 0) (thrBase a r four L target NI (fun i => A3 (pubPort NI i))
        (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0)) e3).mpr sk
  set A4 := thrBase a r four L target NI (fun i => A3 (pubPort NI i)) (fun i => A3 (initPort NI i))
    (fun i => A3 (rcpPort NI i)) C cC hF 0 with hA4
  obtain ⟨rp, ri, rr, rc⟩ := thr_base_rc a r four L target NI (fun i => A3 (pubPort NI i))
    (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0
  have bp : (fun i => A4 (pubPort NI i)) = (fun i => A3 (pubPort NI i)) := funext rp
  have bi : (fun i => A4 (initPort NI i)) = (fun i => A3 (initPort NI i)) := funext ri
  have bc : (fun i => A4 (rcpPort NI i)) = (fun i => A3 (rcpPort NI i)) := funext rc
  refine ⟨A4, s3.seq sk', by rw [bp, bi, bc], ?_, fun x hx1 hx2 => ?_⟩
  · rw [bi]
    exact ThrInitReady.thr_c5 a bnd NI oT h r four L target A3 hW3 hbnd
  · rw [← f3 x hx1 hx2]
    have e3x := congrFun e3 x
    rcases port_cases NI x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact rp i
    · exact ri i
    · rw [hA4, rr i, e3x, KeyZeroMode.thrBlank0_eq]
      unfold KeyZeroMode.keyBlank
      rw [if_neg (by
        intro hm
        obtain ⟨k, -, hk'⟩ := Finset.mem_image.mp hm
        have := congrArg Fin.val hk'
        rw [RowsInit.ThrLoop.master_val, rowpPort_val] at this
        have := i.isLt
        omega)]
      exact ((thr_base_rc a r four L target NI _ _ _ C cC hF 0).2.2.1 i).symm
    · exact rc i
    · have := loop_val NI i; omega
    · have := c6_val NI i; omega
    · have := RowsInit.C5.c5_val NI i; omega

end Main2

/-! ## 5. The THR branch: switch on the nonempty flag (port 150) -/

section Branch
variable (a : DecompositionAlgorithm) (bnd : Request → Fin 4 → ℕ)
  (bndW : (c : Fin 4) → PacketsGlue.RequestMeta.WordStage a
    (fun r => frame (SignedSortKey.binary (r.input a).length (bnd r c))))
  (NI oT o oC : ℕ) (h : 146 ≤ NI)

/-- The nonempty branch: the THR `init` words, then the key-0 branch. -/
def neM := Composition.machine
  (RowsInit.ThrInitRun.machine a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU NI oT) (mainM a NI o oC h)

/-- **The THR branch** (one fixed machine): nonempty family (cell 0 of port 150) → `neM`, else stop. -/
def branchM := CloseoutRowsOriginalSwitch.machine (neM a bnd bndW NI oT o oC h)
  (CloseoutRowsOriginalSwitch.stop (2 + rowsWork NI)) (wp NI 150)

variable (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)

def neCost : ℕ :=
  RowsInit.ThrInitRun.cost a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU (.thr r four L target) + 1 +
    mainCost a r four L target

/-- **Nonempty THR family**: `thrBase … 0` at the bank's own blocks, `ThrC5Ready`, nothing else moved. -/
theorem branch_ne (hT : 150 ≤ oT) (hTo : oT + RowsInit.ThrInitRun.need a bnd bndW ThrSelBase.bcD ThrSelBase.bdD
      ThrSelBase.bcU ThrSelBase.bdU ≤ o) (hNo : o + RowsInit.ThrLoop.need a ≤ oC) (hC : oC + RowsInit.C5.needC a ≤ NI)
    (C cC hF : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.thr r four L target)))
    (hR : ∀ i, A (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hFx : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A x = [])
    (hFl : A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length true)
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + oT ≤ x.val → x.val < 2 + NI → A x = [])
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = [])
    (hbnd : ∀ c, bnd (.thr r four L target) c = ThrSel.bnd a r c)
    (hne : 0 < (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length) :
    ∃ A4 : Fin (2 + rowsWork NI) → List Bool,
      Step (branchM a bnd bndW NI oT o oC h) (neCost a bnd bndW r four L target + 2) (fun _ => 0) A (fun _ => 0) A4 ∧
      A4 = thrBase a r four L target NI (fun i => A4 (pubPort NI i)) (fun i => A4 (initPort NI i))
        (fun i => A4 (rcpPort NI i)) C cC hF 0 ∧
      PartsStep.ThrC5Ready a r four L target NI (fun i => A4 (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.ini NI h) (ThrInitReady.ix NI h) (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h)
        (PrimeReserve.rpOf a (.thr r four L target)) ∧
      (∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 ≤ x.val ∧ x.val < 148) →
        ¬ (2 + oT ≤ x.val ∧ x.val < 2 + NI) → A4 x = A x) := by
  have hkl : 0 < (RCFive.RowKeys.thrKeys a r L target).length := by
    rw [← RCFive.RowKeys.thr_rows_eq a r L target, List.length_map] at hne; exact hne
  obtain ⟨k0, -⟩ := key_head a r L target hkl
  have hU := (ThrSelBase.b_spec a r four L target k0.selection).2
  obtain ⟨A1, s1, w1, w2, w3, w4, w5, w6, f1⟩ := RowsInit.ThrInitRun.words_run a bnd bndW ThrSelBase.bcD ThrSelBase.bdD
    ThrSelBase.bcU ThrSelBase.bdU NI oT (by omega) (by omega) (.thr r four L target) A hU h0 hFx
    (fun x h1 h2 => hI x h1 (by omega))
  have hW : ThrInitReady.WordsAt a bnd ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU NI oT
      (.thr r four L target) A1 :=
    ThrInitReady.wordsAt_of_run a bnd _ _ _ _ NI oT _ A A1 (hFx _ (by rw [wp_val (by rw [rw_eq]; omega)]; omega)
      (by rw [wp_val (by rw [rw_eq]; omega)]; omega)) w1 w2 w3 w4 w5 w6
  have hNT : RowsInit.ThrInitRun.need a bnd bndW ThrSelBase.bcD ThrSelBase.bdD ThrSelBase.bcU ThrSelBase.bdU ≤ o - oT := by
    omega
  obtain ⟨A4, s4, e4, c4, f4⟩ := main_run a NI o oC h r four L target hNo hC (by omega) C cC hF A1
    (by rw [f1 _ (by rw [RowsInit.ThrLoop.pub_val]; simp) (by rw [RowsInit.ThrLoop.pub_val]; simp)]; exact h0)
    (fun i => by
      have := rowpPort_val NI i
      rw [f1 _ (by omega) (by omega)]; exact hR i)
    (fun x h1 h2 => by rw [f1 _ (by omega) (by omega)]; exact hI x (by omega) h2)
    (fun x h1 => by rw [f1 _ (by omega) (by omega)]; exact hB x h1)
    bnd oT (by omega) hW hbnd hkl
  refine ⟨A4, CloseoutRowsOriginalSwitch.true_run _ _ _ (s1.seq s4) (by rw [hFl, cell0_rep]; simp [hne]), e4, c4,
    fun x hx1 hx2 hx3 => ?_⟩
  rw [f4 x hx1 (by omega), f1 x (by omega) (by omega)]

/-- **Empty THR family**: the switch stops; the bank already IS `thrBase … 0` (no key: blank loop, C6, C5). -/
theorem branch_e (C cC hF : ℕ) (A : Fin (2 + rowsWork NI) → List Bool)
    (hR : ∀ i, A (rowpPort NI i) = rowpWords (thrN a r L target) C cC hF i)
    (hFl : A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length true)
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = [])
    (he : (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target).rows.length = 0) :
    Step (branchM a bnd bndW NI oT o oC h) (0 + 2) (fun _ => 0) A (fun _ => 0) A ∧
      A = thrBase a r four L target NI (fun i => A (pubPort NI i)) (fun i => A (initPort NI i))
        (fun i => A (rcpPort NI i)) C cC hF 0 := by
  refine ⟨CloseoutRowsOriginalSwitch.false_run _ _ _ (stop_run _ _) (by rw [hFl, he]; rfl), ?_⟩
  have hkl : (RCFive.RowKeys.thrKeys a r L target).length = 0 := by
    rw [← RCFive.RowKeys.thr_rows_eq a r L target, List.length_map] at he; exact he
  have hk : thrKeyAt a r L target 0 = none := by
    simp only [thrKeyAt, List.length_eq_zero_iff.mp hkl, List.length_nil, Nat.mod_zero, List.getElem?_nil]
  exact thr_shape_none a r four L target NI C cC hF A hk hR hB

end Branch

end
end RowsInit.ThrWork
