import Proof.Rows.RowsKeySucc

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeyTop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc
noncomputable section

/-! ## 1. Ports and slot maps -/

/-- The work port of cell-bank tape `c` of the loop block (cells 0–253 `0^R`, clock 254 `1^R`, log 255 `0^(R+1)`). -/
def cellPort (NI : Nat) (c : Fin 257) : Fin (2+rowsWork NI) :=
  loopPort NI (((RowsConstruction.ThrCell.cellP c).castAdd 1).castAdd 1)

theorem masterPort_val (NI : Nat) (k : Fin 254) : (masterPort NI k).val = 2+NI+72+257+k.val := by
  simp [masterPort, loopPort, fixPort, RowsConstruction.ThrCell.masterP, RowsConstruction.CellReload.masterPort]
  omega

theorem cellPort_val (NI : Nat) (c : Fin 257) : (cellPort NI c).val = 2+NI+72+c.val := by
  simp [cellPort, loopPort, fixPort, RowsConstruction.ThrCell.cellP, RowsConstruction.CellReload.cellPort]
  omega

theorem c5Port_val (NI : Nat) (i : Fin 16) : (c5Port NI i).val = 2+NI+594+i.val := by
  simp [c5Port, fixPort, RowsConstruction.ThrCell.MT]
  omega

/-- Residue level: digit master 242, bound master 240 (the prime), flag and scratch cells 0–3, clock 254, log 255. -/
def slR (NI : Nat) : Fin 8 → Fin (2+rowsWork NI) :=
  ![masterPort NI 242, masterPort NI 240, cellPort NI 0, cellPort NI 1, cellPort NI 2, cellPort NI 3,
    cellPort NI 254, cellPort NI 255]

/-- Seed level: digit C5 port 0, bound C5 port 1 (the seed count), flag and scratch C5 7–10, driver 11, log 12. -/
def slS (NI : Nat) : Fin 8 → Fin (2+rowsWork NI) :=
  ![c5Port NI 0, c5Port NI 1, c5Port NI 7, c5Port NI 8, c5Port NI 9, c5Port NI 10, c5Port NI 11, c5Port NI 12]

theorem slR_injective (NI : Nat) : Function.Injective (slR NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [slR, masterPort_val, cellPort_val] at hv ⊢

theorem slS_injective (NI : Nat) : Function.Injective (slS NI) := by
  intro x y h
  have hv := congrArg Fin.val h
  fin_cases x <;> fin_cases y <;> simp [slS, c5Port_val] at hv ⊢

theorem c5_ne_master (NI : Nat) (i : Fin 16) (k : Fin 254) : c5Port NI i ≠ masterPort NI k := by
  intro h
  have hv := congrArg Fin.val h
  rw [c5Port_val, masterPort_val] at hv
  have := i.isLt
  have := k.isLt
  omega

/-- **The THR C5 top machine** (for a fixed continuation `K`). -/
def thrTop (NI : Nat) {sK : Nat} (K : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) sK) :=
  digitStep (slR NI) (digitStep (slS NI) K)

/-- The cost of a carried digit step at width `w` and blank size `R`, continuing with a stage of cost `n`. -/
def carryCost (w R n : Nat) : Nat := 4*w+2+1+((4*w+4)+1+(((2*(2*w+1)+2)+1+((2*R+4)+1+n))+2))

/-! ## 2. Bank identities of the work layout -/

section Bank
variable {NI : Nat} (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rowp : Fin 8 → List Bool)
  (rcp : Fin 64 → List Bool) (c6 : Fin 2 → List Bool)

theorem wl_master (c5 : Fin 16 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
    (M : Fin 254 → List Bool) (k : Fin 254) :
    workLayout pub init rowp rcp (loopBank live R M) c6 c5 (masterPort NI k) = M k := by
  simp only [masterPort, layout_loop, loopBank, Fin.addCases_left, RowsConstruction.ThrCell.tapes,
    RowsConstruction.ThrCell.layout_master]

theorem wl_cell (c5 : Fin 16 → List Bool) {q : Nat} (live : Finset (Fin q)) (R : Nat)
    (M : Fin 254 → List Bool) (c : Fin 257) :
    workLayout pub init rowp rcp (loopBank live R M) c6 c5 (cellPort NI c) =
      PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R
        (List.replicate (2^liveᶜ.card) false) c := by
  simp only [cellPort, layout_loop, loopBank, Fin.addCases_left, RowsConstruction.ThrCell.tapes,
    RowsConstruction.ThrCell.layout_cell]

theorem wl_loop_update (c5 : Fin 16 → List Bool) (loop : Fin (RowsConstruction.ThrCell.MT+1+1) → List Bool)
    (i : Fin (RowsConstruction.ThrCell.MT+1+1)) (v : List Bool) :
    workLayout pub init rowp rcp (Function.update loop i v) c6 c5 =
      Function.update (workLayout pub init rowp rcp loop c6 c5) (loopPort NI i) v := by
  unfold workLayout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_left,
    RowsConstruction.CellInput.addCases_update_left, RowsConstruction.CellInput.addCases_update_right,
    RowsConstruction.CellInput.addCases_update_right]
  rfl

theorem wl_c5_update (loop : Fin (RowsConstruction.ThrCell.MT+1+1) → List Bool) (c5 : Fin 16 → List Bool)
    (i : Fin 16) (v : List Bool) :
    workLayout pub init rowp rcp loop c6 (Function.update c5 i v) =
      Function.update (workLayout pub init rowp rcp loop c6 c5) (c5Port NI i) v := by
  unfold workLayout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_right,
    RowsConstruction.CellInput.addCases_update_right]
  rfl

end Bank

theorem loopBank_update {q : Nat} (live : Finset (Fin q)) (R : Nat) (M : Fin 254 → List Bool) (k : Fin 254)
    (v : List Bool) :
    loopBank live R (Function.update M k v) =
      Function.update (loopBank live R M) (((RowsConstruction.ThrCell.masterP k).castAdd 1).castAdd 1) v := by
  unfold loopBank RowsConstruction.ThrCell.tapes RowsConstruction.ThrCell.layout RowsConstruction.CellReload.layout
  rw [RowsConstruction.CellInput.addCases_update_right, RowsConstruction.CellInput.addCases_update_left,
    RowsConstruction.CellInput.addCases_update_left, RowsConstruction.CellInput.addCases_update_left]
  rfl

theorem c5_seed_update (e e' N : Nat) (cut : List Bool) (off : Fin 4 → List Bool) (S : Nat) :
    c5Words (seedWords e' N) cut off S =
      Function.update (c5Words (seedWords e N) cut off S) 0 (fb (natBitLength N) e') := by
  funext i
  fin_cases i <;> rfl

/-! ## 3. The key facts at the THR request -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The THR framed width. -/
abbrev wT : Nat := 12*RowsConstruction.ThrWidth.T a r four L target+19
/-- The loop block's blank size (the cell reserve). -/
abbrev RT : Nat := thrRes r.q (RowsConstruction.ThrWidth.T a r four L target)
/-- The seed count. -/
abbrev NS : Nat := (thrSeeds a r L target).length

theorem keyAt_eq (j : Nat) (hj : j < (KeySucc.keys a r L target).length) :
    thrKeyAt a r L target j = some (KeySucc.keys a r L target)[j] := by
  simp only [thrKeyAt, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj]

theorem masters_242 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 242 = fb (wT a r four L target) k.residue.val := by
  unfold thrMasters
  rw [if_neg (by decide), keyPad_key _ (by decide)]
  exact thr_242 a r four _ _ L target _ _ _ _ _ _ _ _

theorem masters_240 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 240 = fb (wT a r four L target) k.prime.val := by
  unfold thrMasters
  rw [if_neg (by decide), keyPad_key _ (by decide)]
  exact thr_prime_ports a r four _ _ L target _ _ _ _ _ _ _ _ 240 (Or.inr (Or.inr rfl))

theorem wT_fits (k : RCFive.RowKeys.ThrKey a r L target) :
    2*wT a r four L target+1 ≤ RT a r four L target := by
  have h := thr_hml a r four L target (RT a r four L target) (thrR_le_res _ _) k 242
  rw [masters_242, fb, frame_length, SignedSortKey.binary_length] at h
  exact h

theorem prime_lt (k : RCFive.RowKeys.ThrKey a r L target) : k.prime.val < 2^(wT a r four L target) := by
  show k.prime.val < 2^(12*RowsConstruction.ThrWidth.T a r four L target+19)
  have h := RowsConstruction.ThrWidth.prime_fit a r four L target _ rfl k.prime
  have := k.residue.isLt
  omega

theorem seedIdx_lt (k : RCFive.RowKeys.ThrKey a r L target) :
    thrSeedIdx a r L target k < NS a r L target := by
  simp only [thrSeedIdx, NS, thrSeeds, PCJ9eff70d512234a4c_Fixed.Packets.seedList, List.length_ofFn]
  exact Fin.isLt _

theorem seed_lt : NS a r L target < 2^(natBitLength (NS a r L target)) :=
  Nat.lt_pow_succ_log_self (by decide) _

/-! ## 4. The carry cascade on the last key and the two closed cases -/

theorem next_R (d : Fin 8 → ℕ) (hb : d 6 + 1 < primeAt (cut a r target) (d 4)) :
    next (spec a r four L target) d = some (Function.update d 6 (d 6 + 1)) := by
  have hR : next [Rl a r target] d = some (Function.update d 6 (d 6 + 1)) := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl, zero]
    rw [if_pos hb]
  have e := next_append_of_some (coords a r four ++ [Pl a r target, Sl a r L target]) [Rl a r target] _ _ hR
  rw [List.append_assoc] at e
  exact e

theorem next_S (d : Fin 8 → ℕ) (hb : ¬ d 6 + 1 < primeAt (cut a r target) (d 4))
    (hs : d 5 + 1 < (thrSeeds a r L target).length) :
    next (spec a r four L target) d = some (Function.update (Function.update d 5 (d 5 + 1)) 6 0) := by
  have hR : next [Rl a r target] d = none := by
    rw [next_cons_of_none _ _ _ rfl]
    simp only [Rl]
    rw [if_neg hb]
  have hS : next [Sl a r L target, Rl a r target] d =
      some (Function.update (Function.update d 5 (d 5 + 1)) 6 0) := by
    rw [next_cons_of_none _ _ _ hR]
    simp only [Sl, Rl, zero]
    rw [if_pos hs]
  have e := next_append_of_some (coords a r four ++ [Pl a r target]) [Sl a r L target, Rl a r target] _ _ hS
  rw [List.append_assoc] at e
  exact e

/-- The last key's digits have no successor. -/
theorem last_none (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (hl : j+1 = (KeySucc.keys a r L target).length) :
    next (spec a r four L target) (dig a r L target (KeySucc.keys a r L target)[j]) = none := by
  have hne : PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target) ≠ [] := by
    change KeySucc.keys a r L target ≠ []
    intro h
    rw [h] at hj
    simp at hj
  have hl' := (enum_next (spec a r four L target) (cursorSpec_wf a _) (cursorSpec_pos a _ hne) (fun _ => 0)).2.1
  rw [← thr_digits a r four L target] at hl'
  apply hl'
  have e : (KeySucc.keys a r L target).length - 1 = j := by omega
  rw [List.getLast?_eq_getElem?, List.length_map, e, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

include four in
theorem last_res (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (hl : j+1 = (KeySucc.keys a r L target).length) :
    ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val := by
  intro h
  have e := next_R a r four L target (dig a r L target (KeySucc.keys a r L target)[j])
    (by rw [dig_res a r four, primeAt_dig a r four]; exact h)
  rw [last_none a r four L target j hj hl] at e
  exact Option.some_ne_none _ e.symm

include four in
theorem last_seed (j : Nat) (hj : j < (KeySucc.keys a r L target).length)
    (hl : j+1 = (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val) :
    ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length := by
  intro h
  have e := next_S a r four L target (dig a r L target (KeySucc.keys a r L target)[j])
    (by rw [dig_res a r four, primeAt_dig a r four]; exact h1) (by rw [dig_seed a r four]; exact h)
  rw [last_none a r four L target j hj hl] at e
  exact Option.some_ne_none _ e.symm

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

theorem base_eq (j : Nat) (hj : j < (KeySucc.keys a r L target).length) :
    thrBase a r four L target NI pub init rcp C cC hF j =
      workLayout pub init (rowpWords (thrN a r L target) C cC hF) rcp
        (loopBank (thrLive r L) (RT a r four L target)
          (thrMasters a r four L target (RT a r four L target) (KeySucc.keys a r L target)[j]))
        (c6Words (thrLive r L)ᶜ.card)
        (c5Words (seedWords (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) (NS a r L target))
          (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
          (seedScratch (NS a r L target))) := by
  simp only [thrBase, keyAt_eq a r L target j hj]

/-- **Case R at bank level**: the residue advances; only master 242 changes. -/
theorem base_succR (j : Nat) (hj : j+1 < (KeySucc.keys a r L target).length)
    (h : (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val) :
    thrBase a r four L target NI pub init rcp C cC hF (j+1) =
      Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242)
        (fb (wT a r four L target) ((KeySucc.keys a r L target)[j].residue.val + 1)) := by
  obtain ⟨hs, hp, he, hr⟩ := thr_keyR a r four L target j hj h
  rw [base_eq a r four L target NI pub init rcp C cC hF j (by omega),
    base_eq a r four L target NI pub init rcp C cC hF (j+1) hj,
    masters_same a r four L target _ _ _ hs hp, hr, he, loopBank_update, wl_loop_update]
  rfl

/-- **Case S at bank level**: the residue wraps to `0`, the seed index advances. -/
theorem base_succS (j : Nat) (hj : j+1 < (KeySucc.keys a r L target).length)
    (h1 : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val)
    (h2 : thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length) :
    thrBase a r four L target NI pub init rcp C cC hF (j+1) =
      Function.update (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242)
        (fb (wT a r four L target) 0)) (c5Port NI 0)
        (fb (natBitLength (NS a r L target)) (thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1)) := by
  obtain ⟨hs, hp, he, hr⟩ := thr_keyS a r four L target j hj h1 h2
  rw [base_eq a r four L target NI pub init rcp C cC hF j (by omega),
    base_eq a r four L target NI pub init rcp C cC hF (j+1) hj,
    masters_same a r four L target _ _ _ hs hp, hr, he,
    c5_seed_update (thrSeedIdx a r L target (KeySucc.keys a r L target)[j])
      (thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1),
    wl_c5_update, loopBank_update, wl_loop_update]
  rfl

/-! ## 5. The top machine -/

theorem readyR (j : Nat) (hj : j < (KeySucc.keys a r L target).length) :
    Ready (slR NI) (wT a r four L target) (RT a r four L target) (fun _ => 0)
      (thrBase a r four L target NI pub init rcp C cC hF j) := by
  rw [base_eq a r four L target NI pub init rcp C cC hF j hj]
  exact {
    heads := fun _ => rfl
    flag := by rw [show slR NI 2 = cellPort NI 0 from rfl, wl_cell]; rfl
    capI := by rw [show slR NI 3 = cellPort NI 1 from rfl, wl_cell]; rfl
    capC := by rw [show slR NI 4 = cellPort NI 2 from rfl, wl_cell]; rfl
    capL := by rw [show slR NI 5 = cellPort NI 3 from rfl, wl_cell]; rfl
    drv := by rw [show slR NI 6 = cellPort NI 254 from rfl, wl_cell]; rfl
    log := by rw [show slR NI 7 = cellPort NI 255 from rfl, wl_cell]; rfl
    hR := wT_fits a r four L target (KeySucc.keys a r L target)[j] }

theorem readyS (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (v : List Bool) :
    Ready (slS NI) (natBitLength (NS a r L target)) (seedScratch (NS a r L target)) (fun _ => 0)
      (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242) v) := by
  have e : ∀ i : Fin 16, Function.update (thrBase a r four L target NI pub init rcp C cC hF j)
      (masterPort NI 242) v (c5Port NI i) =
      c5Words (seedWords (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) (NS a r L target))
        (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
        (seedScratch (NS a r L target)) i := by
    intro i
    rw [Function.update_of_ne (c5_ne_master NI i 242), base_eq a r four L target NI pub init rcp C cC hF j hj,
      layout_c5]
  exact {
    heads := fun _ => rfl
    flag := by rw [show slS NI 2 = c5Port NI 7 from rfl, e]; rfl
    capI := by rw [show slS NI 3 = c5Port NI 8 from rfl, e]; rfl
    capC := by rw [show slS NI 4 = c5Port NI 9 from rfl, e]; rfl
    capL := by rw [show slS NI 5 = c5Port NI 10 from rfl, e]; rfl
    drv := by rw [show slS NI 6 = c5Port NI 11 from rfl, e]; rfl
    log := by rw [show slS NI 7 = c5Port NI 12 from rfl, e]; rfl
    hR := by simp only [seedScratch]; omega }

theorem seed_at (j : Nat) (hj : j < (KeySucc.keys a r L target).length) (v : List Bool) (i : Fin 2) :
    Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242) v
      (slS NI (i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) =
    seedWords (thrSeedIdx a r L target (KeySucc.keys a r L target)[j]) (NS a r L target) i := by
  fin_cases i
  · rw [show slS NI _ = c5Port NI 0 from rfl, Function.update_of_ne (c5_ne_master NI 0 242),
      base_eq a r four L target NI pub init rcp C cC hF j hj, layout_c5]
    rfl
  · rw [show slS NI _ = c5Port NI 1 from rfl, Function.update_of_ne (c5_ne_master NI 1 242),
      base_eq a r four L target NI pub init rcp C cC hF j hj, layout_c5]
    rfl

/-- **THR C5, residue and seed levels.** For every row `j` of the THR family, the fixed machine `thrTop NI K` runs
from `thrBase j` to `thrBase (j+1)`, all heads `0`. Its only premise is `K`'s own step when the residue and the
seed both overflow (the prime/selection levels; on the last row this is the wrap to key `0`). -/
theorem thr_top (j : Nat) (hj : j < (KeySucc.keys a r L target).length) {sK : Nat}
    (K : NearCubicWires.LocalBitMultitape.Machine (2+rowsWork NI) sK) (nK : Nat)
    (hK : ¬ (KeySucc.keys a r L target)[j].residue.val + 1 < (KeySucc.keys a r L target)[j].prime.val →
      ¬ thrSeedIdx a r L target (KeySucc.keys a r L target)[j] + 1 < (thrSeeds a r L target).length →
      NearCubicWires.ExtDecompositionBatch.Step K nK (fun _ => 0)
        (Function.update (Function.update (thrBase a r four L target NI pub init rcp C cC hF j) (masterPort NI 242)
          (fb (wT a r four L target) 0)) (c5Port NI 0) (fb (natBitLength (NS a r L target)) 0))
        (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF (j+1))) :
    NearCubicWires.ExtDecompositionBatch.Step (thrTop NI K)
      (carryCost (wT a r four L target) (RT a r four L target)
        (carryCost (natBitLength (NS a r L target)) (seedScratch (NS a r L target)) nK))
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF j)
      (fun _ => 0) (thrBase a r four L target NI pub init rcp C cC hF (j+1)) := by
  set B := thrBase a r four L target NI pub init rcp C cC hF j with hBdef
  set k := (KeySucc.keys a r L target)[j] with hkdef
  have hX : B (slR NI 0) = fb (wT a r four L target) k.residue.val := by
    rw [show slR NI 0 = masterPort NI 242 from rfl, hBdef, base_eq a r four L target NI pub init rcp C cC hF j hj,
      wl_master, masters_242]
  have hBd : B (slR NI 1) = fb (wT a r four L target) k.prime.val := by
    rw [show slR NI 1 = masterPort NI 240 from rfl, hBdef, base_eq a r four L target NI pub init rcp C cC hF j hj,
      wl_master, masters_240]
  have hb := prime_lt a r four L target k
  have hres := k.residue.isLt
  have hRd := readyR a r four L target NI pub init rcp C cC hF j hj
  by_cases hR : k.residue.val + 1 < k.prime.val
  · have hj1 : j+1 < (KeySucc.keys a r L target).length := by
      by_contra hn
      exact last_res a r four L target j hj (by omega) hR
    have s := digit_noCarry (slR NI) (slR_injective NI) (digitStep (slS NI) K) (wT a r four L target)
      k.residue.val k.prime.val (RT a r four L target) (fun _ => 0) B hRd hX hBd hR hb
    rw [show slR NI 0 = masterPort NI 242 from rfl,
      ← base_succR a r four L target NI pub init rcp C cC hF j hj1 hR] at s
    exact s.enlarge (by unfold carryCost; omega)
  · have hxb : k.residue.val + 1 = k.prime.val := by omega
    have hS0 := seed_at a r four L target NI pub init rcp C cC hF j hj (fb (wT a r four L target) 0) 0
    have hS1 := seed_at a r four L target NI pub init rcp C cC hF j hj (fb (wT a r four L target) 0) 1
    have hRS := readyS a r four L target NI pub init rcp C cC hF j hj (fb (wT a r four L target) 0)
    have hsl := seedIdx_lt a r L target k
    have hsN := seed_lt a r L target
    by_cases hS : thrSeedIdx a r L target k + 1 < (thrSeeds a r L target).length
    · have hj1 : j+1 < (KeySucc.keys a r L target).length := by
        by_contra hn
        exact last_seed a r four L target j hj (by omega) hR hS
      have s2 := digit_noCarry (slS NI) (slS_injective NI) K (natBitLength (NS a r L target))
        (thrSeedIdx a r L target k) (NS a r L target) (seedScratch (NS a r L target)) (fun _ => 0)
        (Function.update B (masterPort NI 242) (fb (wT a r four L target) 0)) hRS hS0 hS1 hS hsN
      rw [show slS NI 0 = c5Port NI 0 from rfl,
        ← base_succS a r four L target NI pub init rcp C cC hF j hj1 hR hS] at s2
      have s := digit_carry (slR NI) (slR_injective NI) (digitStep (slS NI) K) (wT a r four L target)
        k.residue.val k.prime.val (RT a r four L target) _ (fun _ => 0) (fun _ => 0) B _ hRd hX hBd hxb hb
        (by rw [show slR NI 0 = masterPort NI 242 from rfl]; exact s2)
      exact s.enlarge (by unfold carryCost; omega)
    · have hxS : thrSeedIdx a r L target k + 1 = NS a r L target := by
        have h' : thrSeedIdx a r L target k < (thrSeeds a r L target).length := hsl
        show thrSeedIdx a r L target k + 1 = (thrSeeds a r L target).length
        omega
      have s2 := digit_carry (slS NI) (slS_injective NI) K (natBitLength (NS a r L target))
        (thrSeedIdx a r L target k) (NS a r L target) (seedScratch (NS a r L target)) nK (fun _ => 0) (fun _ => 0)
        (Function.update B (masterPort NI 242) (fb (wT a r four L target) 0)) _ hRS hS0 hS1 hxS hsN
        (by rw [show slS NI 0 = c5Port NI 0 from rfl]; exact hK hR hS)
      have s := digit_carry (slR NI) (slR_injective NI) (digitStep (slS NI) K) (wT a r four L target)
        k.residue.val k.prime.val (RT a r four L target) _ (fun _ => 0) (fun _ => 0) B _ hRd hX hBd hxb hb
        (by rw [show slR NI 0 = masterPort NI 242 from rfl]; exact s2)
      exact s.enlarge (by unfold carryCost; omega)

end Thr

end
end RowsConstruction.KeyTop
