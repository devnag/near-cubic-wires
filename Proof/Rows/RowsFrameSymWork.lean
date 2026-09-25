import Proof.Rows.RowsFrameSymC5
import Proof.Rows.RowsInitWorkPhase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.FrameSymWork
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout RowsConstruction.ThrCell
open RowsInit.ThrLoop (wp wp_val rw_eq loop_val c6_val master_val pub_val)
open RowsInit.ThrWork (port_cases stop_run cell0_rep)
noncomputable section

/-- **The SYM loop block + C6 of `symBase … 0`, the four SYM key masters left blank** — the exact SYM twin of RX's
`ThrLoop.loop_run`, as RS publishes it (`RowsInit.SymLoop.need/machine/cost/loop_run`). -/
structure SymLoopIn (a : DecompositionAlgorithm) where
  need : ℕ
  states : ℕ → ℕ → ℕ
  machine : (NI o : ℕ) → Machine (2 + rowsWork NI) (states NI o)
  cost : Request → ℕ
  loop_run : ∀ (NI o : ℕ), o + need ≤ NI → ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k0 : RCFive.RowKeys.SymKey r L target)
    (A : Fin (2 + rowsWork NI) → List Bool),
    A (pubPort NI 0) = frame (Request.input a (.sym r four L target)) →
    (∀ x : Fin (2 + rowsWork NI), 2 + o ≤ x.val → x.val < 2 + o + need → A x = []) →
    (∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → x.val < 2 + NI + 594 → A x = []) →
    ∃ A' : Fin (2 + rowsWork NI) → List Bool,
      Step (machine NI o) (cost (.sym r four L target)) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k ∈ symKeySet, A' (masterPort NI k) = []) ∧
      (∀ i : Fin (MT+1+1), (∀ k ∈ symKeySet, loopPort NI i ≠ masterPort NI k) →
        A' (loopPort NI i) = loopBank (symLive r L) (symRes r.q (symT a r four L target))
          (symMasters a r four L target (symRes r.q (symT a r four L target)) k0) i) ∧
      (∀ i, A' (c6Port NI i) = c6Words (symLive r L)ᶜ.card i) ∧
      (∀ x : Fin (2 + rowsWork NI), ¬ (2 + o ≤ x.val ∧ x.val < 2 + o + need) →
        ¬ (2 + NI + 72 ≤ x.val ∧ x.val < 2 + NI + 594) → A' x = A x)

/-! ## 1. The shape of `symBase … 0` (with and without a first key) -/

section Shape
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target NI C cC hF : ℕ) (X : Fin (2 + rowsWork NI) → List Bool)

/-- A bank with row 0's blocks, the four SYM key masters blank, IS `symBlank0` of `symBase … 0` at its own `pub/init/rcp`. -/
theorem sym_shape (k0 : RCFive.RowKeys.SymKey r L target) (hk : symKeyAt r L target 0 = some k0)
    (hR : ∀ i, X (rowpPort NI i) = rowpWords (symN r L target) C cC hF i)
    (hK : ∀ k ∈ symKeySet, X (masterPort NI k) = [])
    (hL : ∀ i, (∀ k ∈ symKeySet, loopPort NI i ≠ masterPort NI k) → X (loopPort NI i) =
      loopBank (symLive r L) (symRes r.q (symT a r four L target))
        (symMasters a r four L target (symRes r.q (symT a r four L target)) k0) i)
    (h6 : ∀ i, X (c6Port NI i) = c6Words (symLive r L)ᶜ.card i)
    (h5 : ∀ i, X (c5Port NI i) = c5Words (seedWords (symSeedIdx r L target k0) (symSeeds r L target).length) []
      (symOffWords r L target (symT a r four L target) k0) (seedScratch (symSeeds r L target).length) i) :
    X = KeyZero.symBlank0 NI (symBase a r four L target NI (fun i => X (pubPort NI i)) (fun i => X (initPort NI i))
      (fun i => X (rcpPort NI i)) C cC hF 0) := by
  funext p
  rw [KeyZeroMode.symBlank0_eq]
  unfold KeyZeroMode.keyBlank
  split_ifs with hp
  · obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp hp
    exact hK k hk'
  · rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [symBase, hk, layout_pub]
    · simp only [symBase, hk, layout_init]
    · simp only [symBase, hk, layout_rowp]; exact hR i
    · simp only [symBase, hk, layout_rcp]
    · simp only [symBase, hk, layout_loop]
      exact hL i (fun k hk' he => hp (Finset.mem_image.mpr ⟨k, hk', he.symm⟩))
    · simp only [symBase, hk, layout_c6]; exact h6 i
    · simp only [symBase, hk, layout_c5]; exact h5 i

/-- Without a first key (empty family), `symBase … 0` has blank loop, C6 and C5 blocks. -/
theorem sym_shape_none (hk : symKeyAt r L target 0 = none)
    (hR : ∀ i, X (rowpPort NI i) = rowpWords (symN r L target) C cC hF i)
    (hB : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → X x = []) :
    X = symBase a r four L target NI (fun i => X (pubPort NI i)) (fun i => X (initPort NI i))
      (fun i => X (rcpPort NI i)) C cC hF 0 := by
  funext p
  rcases port_cases NI p with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [symBase, hk, layout_pub]
  · simp only [symBase, hk, layout_init]
  · simp only [symBase, hk, layout_rowp]; exact hR i
  · simp only [symBase, hk, layout_rcp]
  · simp only [symBase, hk, layout_loop]; exact hB _ (by rw [loop_val]; omega)
  · simp only [symBase, hk, layout_c6]; exact hB _ (by rw [c6_val]; omega)
  · simp only [symBase, hk, layout_c5]; exact hB _ (by rw [RowsInit.C5.c5_val]; omega)

theorem key_head (hne : 0 < (RCFive.RowKeys.symKeys r L target).length) :
    ∃ k0, symKeyAt r L target 0 = some k0 := by
  refine ⟨(RCFive.RowKeys.symKeys r L target)[0], ?_⟩
  simp only [symKeyAt, Nat.zero_mod, List.getElem?_eq_getElem hne]

end Shape

/-! ## 2. The machine -/

section Machine
variable (a : DecompositionAlgorithm) (Lp : SymLoopIn a) (NI : ℕ) (h : 146 ≤ NI)

/-- Loop block + C6 (RS) ; C5 (RX). -/
def preM (o oC : ℕ) := Composition.machine (Lp.machine NI o) (RowsInit.C5.machine a NI oC)

/-- ; RC5's key-0 writer at RX's fixed index maps. -/
def mainM (o oC : ℕ) := Composition.machine (preM a Lp NI o oC)
  (KeyZeroMode.k0 NI (ThrInitReady.iMode NI h) (ThrInitReady.iz NI h) (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h)
    (ThrInitReady.iniS NI h))

/-- The nonempty branch: the SYM words, then the key-0 branch. -/
def neM (oB : ℕ) := Composition.machine (RowsInit.FrameSymWords.machine a NI oB)
  (mainM a Lp NI h (oB + RowsInit.FrameSymWords.needW a) (oB + RowsInit.FrameSymWords.needW a + Lp.need))

/-- **The SYM branch** (one fixed machine): nonempty family (cell 0 of port 150) → `neM`, else stop. -/
def branchM (oB : ℕ) := CloseoutRowsOriginalSwitch.machine (neM a Lp NI h oB)
  (CloseoutRowsOriginalSwitch.stop (2 + rowsWork NI)) (wp NI 150)

end Machine

/-- The scratch the SYM branch needs past `oB`. -/
def needS (a : DecompositionAlgorithm) (Lp : SymLoopIn a) : ℕ :=
  RowsInit.FrameSymWords.needW a + Lp.need + RowsInit.C5.needC a

/-- The nonempty branch's cost (before the switch). -/
def neCost (a : DecompositionAlgorithm) (Lp : SymLoopIn a) (r : Request) : ℕ :=
  RowsInit.FrameSymWords.cost a r + 1 + ((Lp.cost r + 1 + RowsInit.C5.cost a r) + 1 + KeyZeroMode.k0Cost a r)

/-! ## 3. The two runs -/

section Runs
variable (a : DecompositionAlgorithm) (Lp : SymLoopIn a) (NI : ℕ) (h : 146 ≤ NI) (oB : ℕ)
  (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target C cC hF : ℕ)

/-- **Nonempty SYM family**: `symBase … 0` at the bank's own blocks, `SymC5Ready`, nothing else below `2+NI+72` moved outside
`[2,148)` and `[2+oB, 2+NI)`. -/
theorem branch_ne (hB : 150 ≤ oB) (hS : oB + needS a Lp ≤ NI) (A : Fin (2 + rowsWork NI) → List Bool)
    (h0 : A (pubPort NI 0) = frame (Request.input a (.sym r four L target)))
    (hR : ∀ i, A (rowpPort NI i) = rowpWords (symN r L target) C cC hF i)
    (hFx : ∀ x : Fin (2 + rowsWork NI), 2 ≤ x.val → x.val < 148 → A x = [])
    (hFl : A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length true)
    (hI : ∀ x : Fin (2 + rowsWork NI), 2 + oB ≤ x.val → x.val < 2 + NI → A x = [])
    (hBl : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = [])
    (hne : 0 < (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length) :
    ∃ B : Fin (2 + rowsWork NI) → List Bool,
      Step (branchM a Lp NI h oB) (neCost a Lp (.sym r four L target) + 2) (fun _ => 0) A (fun _ => 0) B ∧
      B = symBase a r four L target NI (fun i => B (pubPort NI i)) (fun i => B (initPort NI i))
        (fun i => B (rcpPort NI i)) C cC hF 0 ∧
      PartsStep.SymC5Ready a r four L target NI (fun i => B (initPort NI i)) (ThrInitReady.iMode NI h)
        (ThrInitReady.iniS NI h) ∧
      (∀ x : Fin (2 + rowsWork NI), x.val < 2 + NI + 72 → ¬ (2 ≤ x.val ∧ x.val < 148) →
        ¬ (2 + oB ≤ x.val ∧ x.val < 2 + NI) → B x = A x) := by
  unfold needS at hS
  have hkl : 0 < (RCFive.RowKeys.symKeys r L target).length := by
    rw [← RCFive.RowKeys.sym_rows_eq r L target, List.length_map] at hne; exact hne
  obtain ⟨k0, hk⟩ := key_head r L target hkl
  have p0 : (pubPort NI 0).val = 0 := rfl
  -- (1) the SYM words
  obtain ⟨A1, s1, w1, w5, f1⟩ := RowsInit.FrameSymWords.words_run a NI oB (by omega) (by omega) (.sym r four L target) A h0
    (fun x h1 h2 => hFx x (by omega) h2)
    (fun i h3 h6 => hBl _ (by rw [RowsInit.FrameSymWords.c5_val]; omega))
    (fun x h1 h2 => hI x h1 (by omega))
  -- (2) RS's loop block + C6
  obtain ⟨A2, s2, hK2, hL2, h62, f2⟩ := Lp.loop_run NI (oB + RowsInit.FrameSymWords.needW a) (by omega) r four L target
    k0 A1
    (by rw [f1 _ (by rw [p0]; omega) (by rw [p0]; omega) (by rw [p0]; omega)]; exact h0)
    (fun x h1 h2 => by rw [f1 x (by omega) (by omega) (by omega)]; exact hI x (by omega) (by omega))
    (fun x h1 h2 => by rw [f1 x (by omega) (by omega) (by omega)]; exact hBl x h1)
  have e20 : A2 (pubPort NI 0) = frame (Request.input a (.sym r four L target)) := by
    rw [f2 _ (by rw [p0]; omega) (by rw [p0]; omega), f1 _ (by rw [p0]; omega) (by rw [p0]; omega) (by rw [p0]; omega)]
    exact h0
  have c5eq : ∀ i : Fin 16, A2 (c5Port NI i) = A1 (c5Port NI i) := fun i => by
    have := RowsInit.C5.c5_val NI i
    exact f2 _ (by omega) (by omega)
  -- (3) RX's C5 writer
  obtain ⟨A3, s3, h012, h7, h11, h12, hz3, f3⟩ := RowsInit.C5.run a NI
    (oB + RowsInit.FrameSymWords.needW a + Lp.need) (by omega) (.sym r four L target) A2 e20
    (fun i hi => by
      have := RowsInit.C5.c5_val NI i
      have hl := i.isLt
      rw [c5eq, f1 _ (by omega) (by omega) (by omega)]
      exact hBl _ (by omega))
    (fun x h1 h2 => by
      rw [f2 _ (by omega) (by omega), f1 _ (by omega) (by omega) (by omega)]
      exact hI x (by omega) (by omega))
  -- frame chain below the loop block
  have f321 : ∀ x : Fin (2 + rowsWork NI), ¬ (2 + NI + 72 ≤ x.val ∧ x.val < 2 + NI + 610) →
      ¬ (2 + oB ≤ x.val ∧ x.val < 2 + NI) → ¬ (138 ≤ x.val ∧ x.val < 148) → A3 x = A x := by
    intro x hx1 hx2 hx3
    rw [f3 x (by omega) (by omega), f2 x (by omega) (by omega), f1 x (by omega) (by omega) (by omega)]
  have hR3 : ∀ i, A3 (rowpPort NI i) = rowpWords (symN r L target) C cC hF i := by
    intro i
    have hv := rowpPort_val NI i
    have hi := i.isLt
    rw [f321 _ (by omega) (by omega) (by omega)]
    exact hR i
  -- (4) the bank IS `symBlank0` of `symBase … 0`
  have e3 : A3 = KeyZero.symBlank0 NI (symBase a r four L target NI (fun i => A3 (pubPort NI i))
      (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0) := by
    refine sym_shape a r four L target NI C cC hF A3 k0 hk hR3 (fun k hk' => ?_) (fun i hi => ?_) (fun i => ?_) ?_
    · have hv := master_val NI k
      have hl := k.isLt
      rw [f3 _ (by omega) (by omega)]
      exact hK2 k hk'
    · have hv := loop_val NI i
      have hl := i.isLt
      simp only [MT] at hl
      rw [f3 _ (by omega) (by omega)]
      exact hL2 i hi
    · have hv := c6_val NI i
      have hl := i.isLt
      rw [f3 _ (by omega) (by omega)]
      exact h62 i
    · refine RowsInit.FrameSymC5.sym_block a r four L target NI A3 k0 hk h012 h7 h11 h12 (fun i h3 h6 => ?_) (fun i hi => ?_)
      · rw [hz3 i (Or.inl ⟨h3, h6⟩), c5eq]
        exact w5 i h3 h6
      · have := RowsInit.C5.c5_val NI i
        have hl := i.isLt
        rw [hz3 i (Or.inr hi), c5eq, f1 _ (by omega) (by omega) (by omega)]
        exact hBl _ (by omega)
  -- (5) `SymC5Ready` on the `init` block
  have hw3 : ∀ j : Fin 10, A3 (wp NI (138 + j.val)) =
      RowsInit.FrameSymWords.symWord a ⟨j.val, by omega⟩ (.sym r four L target) := by
    intro j
    have hj := j.isLt
    have hv : (wp NI (138 + j.val)).val = 138 + j.val := wp_val (by rw [rw_eq]; omega)
    rw [f3 _ (by omega) (by omega), f2 _ (by omega) (by omega)]
    exact w1 j
  have hc5 := RowsInit.FrameSymWords.sym_ready a r four L target NI h A3 hw3
  obtain ⟨hmode, hinitS⟩ := hc5
  -- (6) RC5's key-0 writer
  have sk := KeyZeroMode.sym_k0 a r four L target NI (fun i => A3 (pubPort NI i)) (fun i => A3 (initPort NI i))
    (fun i => A3 (rcpPort NI i)) C cC hF (ThrInitReady.iMode NI h) hmode (ThrInitReady.iz NI h) (ThrInitReady.ib NI h)
    (ThrInitReady.iOne NI h) (ThrInitReady.iniS NI h) hinitS hkl
  have sk' := (congrArg (fun B => Step (KeyZeroMode.k0 NI (ThrInitReady.iMode NI h) (ThrInitReady.iz NI h)
      (ThrInitReady.ib NI h) (ThrInitReady.iOne NI h) (ThrInitReady.iniS NI h))
      (KeyZero.symK0Cost (SymC5.sw a r four L target) (symRes r.q (symT a r four L target)) + 2)
      (fun _ => 0) B (fun _ => 0) (symBase a r four L target NI (fun i => A3 (pubPort NI i))
        (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0)) e3).mpr sk
  set A4 := symBase a r four L target NI (fun i => A3 (pubPort NI i)) (fun i => A3 (initPort NI i))
    (fun i => A3 (rcpPort NI i)) C cC hF 0 with hA4
  obtain ⟨rp, ri, rr, rc⟩ := sym_base_rc a r four L target NI (fun i => A3 (pubPort NI i))
    (fun i => A3 (initPort NI i)) (fun i => A3 (rcpPort NI i)) C cC hF 0
  have bp : (fun i => A4 (pubPort NI i)) = (fun i => A3 (pubPort NI i)) := funext rp
  have bi : (fun i => A4 (initPort NI i)) = (fun i => A3 (initPort NI i)) := funext ri
  have bc : (fun i => A4 (rcpPort NI i)) = (fun i => A3 (rcpPort NI i)) := funext rc
  have run : Step (neM a Lp NI h oB) (neCost a Lp (.sym r four L target)) (fun _ => 0) A (fun _ => 0) A4 :=
    s1.seq ((s2.seq s3).seq sk')
  refine ⟨A4, CloseoutRowsOriginalSwitch.true_run _ _ _ run (by rw [hFl, cell0_rep]; simp [hne]), by rw [bp, bi, bc],
    ?_, fun x hx1 hx2 hx3 => ?_⟩
  · rw [bi]
    exact RowsInit.FrameSymWords.sym_ready a r four L target NI h A3 hw3
  · rw [← f321 x (by omega) (by omega) (by omega)]
    rcases port_cases NI x with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact rp i
    · exact ri i
    · rw [hA4, rr i]; exact (hR3 i).symm
    · exact rc i
    · have := loop_val NI i; omega
    · have := c6_val NI i; omega
    · have := RowsInit.C5.c5_val NI i; omega

/-- **Empty SYM family**: the switch stops; the bank already IS `symBase … 0` (no key: blank loop, C6, C5). -/
theorem branch_e (A : Fin (2 + rowsWork NI) → List Bool)
    (hR : ∀ i, A (rowpPort NI i) = rowpWords (symN r L target) C cC hF i)
    (hFl : A (wp NI 150) = List.replicate (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length true)
    (hBl : ∀ x : Fin (2 + rowsWork NI), 2 + NI + 72 ≤ x.val → A x = [])
    (he : (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target).rows.length = 0) :
    Step (branchM a Lp NI h oB) (0 + 2) (fun _ => 0) A (fun _ => 0) A ∧
      A = symBase a r four L target NI (fun i => A (pubPort NI i)) (fun i => A (initPort NI i))
        (fun i => A (rcpPort NI i)) C cC hF 0 := by
  refine ⟨CloseoutRowsOriginalSwitch.false_run _ _ _ (stop_run _ _) (by rw [hFl, he]; rfl), ?_⟩
  have hkl : (RCFive.RowKeys.symKeys r L target).length = 0 := by
    rw [← RCFive.RowKeys.sym_rows_eq r L target, List.length_map] at he; exact he
  have hk : symKeyAt r L target 0 = none := by
    simp only [symKeyAt, List.length_eq_zero_iff.mp hkl, List.length_nil, Nat.mod_zero, List.getElem?_nil]
  exact sym_shape_none a r four L target NI C cC hF A hk hR hBl

end Runs

/-! ## 4. RX's `SymSpec` -/

/-- **RX's `SymSpec`** for every `NI oB` with `150 ≤ oB` and `oB + needS a Lp ≤ NI` (RS's loop block `Lp` typed until it lands). -/
def symSpecOf (a : DecompositionAlgorithm) (Lp : SymLoopIn a) (NI oB : ℕ) (h : 146 ≤ NI) (hB : 150 ≤ oB)
    (hS : oB + needS a Lp ≤ NI) : RowsInit.WorkPhase.SymSpec a NI oB h where
  states := _
  machine := branchM a Lp NI h oB
  costNe := fun r => neCost a Lp r + 2
  costE := fun _ => 0 + 2
  run_ne := fun r four L target C cC hF A h0 hR hFx hFl hI hBl hne =>
    branch_ne a Lp NI h oB r four L target C cC hF hB hS A h0 hR hFx hFl hI hBl hne
  run_e := fun r four L target C cC hF A hR hFl hBl he =>
    branch_e a Lp NI h oB r four L target C cC hF A hR hFl hBl he

end
end RowsInit.FrameSymWork
