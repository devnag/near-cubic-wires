import Proof.Packets.PacketsKeysNativeMain
import Proof.Rows.RowsInitCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsKeys.Native
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
open NearCubicWires.SupplierPipeline PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## List bounds -/

theorem len_le_flatMap {β : Type} (l : List β) (f : β → List Bool) (hf : ∀ x, 1 ≤ (f x).length) :
    l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; have := hf x; omega

theorem mem_len_le {β : Type} (l : List β) (f : β → List Bool) (x : β) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem sum_le_flatMap {β : Type} (l : List β) (f : β → List Bool) (g : β → ℕ) (h : ∀ x, g x ≤ (f x).length) :
    (l.map g).sum ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]; have := h x; omega

theorem prod_le_two_pow {β : Type} (l : List β) (g : β → ℕ) : (l.map g).prod ≤ 2 ^ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Nat.pow_add]
    exact Nat.mul_le_mul (Nat.lt_two_pow_self).le ih

theorem prod_le_pow {β : Type} (l : List β) (g : β → ℕ) (B : ℕ) (h : ∀ x ∈ l, g x ≤ B) :
    (l.map g).prod ≤ B ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (B ^ xs.length) B]
    exact Nat.mul_le_mul (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-! ## The SYM payload -/

theorem symWord_pay {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    ∃ rest, symWord c = natWord c.bottomCount ++ rest :=
  ⟨RepairOrdinary.frame (List.ofFn c.top) ++ (List.ofFn c.bottom).flatMap (fun g => RepairOrdinary.frame (bottomWord g)),
    by simp only [symWord, List.append_assoc]⟩

theorem bc_le {q : ℕ} (c : NormalizedSymmetricThresholdCircuit q) :
    c.bottomCount + 1 ≤ (RepairOrdinary.frame (symWord c)).length := by
  rw [RepairOrdinary.frame_length]
  have h := len_le_flatMap (List.ofFn c.bottom) (fun g => RepairOrdinary.frame (bottomWord g))
    (fun x => by rw [RepairOrdinary.frame_length]; omega)
  rw [List.length_ofFn] at h
  simp only [symWord, List.length_append]
  omega

/-! ## The native word of each kind -/

theorem native_term (a : DecompositionAlgorithm) : fields a .terminal 0 = natWord 2 := rfl

theorem native_sym (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    fields a (.sym r four L tg) 0 = hdr 0 r.q L tg r.circuits.length ++
      r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c)) := rfl

theorem native_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    fields a (.thr r four L tg) 0 = hdr 1 r.q L tg r.circuits.length ++
      r.circuits.flatMap (fun c => RepairOrdinary.frame (thrWord c)) := rfl

/-! ## The values -/

/-- `#circuits` (`0` for the terminal sentinel). -/
def nCirc : Request → ℕ
  | .terminal => 0
  | .sym r _ _ _ => r.circuits.length
  | .thr r _ _ _ => r.circuits.length

/-- The SYM coordinate-level sum `Σ (bottomCount_i + 1)`, `0` off SYM. -/
def symSumOf : Request → ℕ
  | .sym r _ _ _ => ∑ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1)
  | _ => 0

theorem symSum_list (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    ∑ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1) =
      (r.circuits.map (fun c => c.bottomCount + 1)).sum := by
  simp only [List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem r.circuits (fun c => c.bottomCount + 1)

theorem symSel_list (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    ∏ i : Fin r.circuits.length, ((r.circuits.get i).bottomCount + 1) =
      (r.circuits.map (fun c => c.bottomCount + 1)).prod := by
  simp only [List.get_eq_getElem]
  exact Fin.prod_univ_fun_getElem r.circuits (fun c => c.bottomCount + 1)

/-! ## The runs, per kind -/

theorem main_sym_req (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    MainResult (fields a (.sym r four L tg) 0) r.circuits.length
      (r.circuits.map (fun c => c.bottomCount + 1)).sum (r.circuits.map (fun c => c.bottomCount + 1)).prod := by
  rw [native_sym]
  set w := hdr 0 r.q L tg r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))
    with hw
  have hsum : (r.circuits.map (fun c => c.bottomCount + 1)).sum ≤ w.length := by
    have := sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (symWord c)) (fun c => c.bottomCount + 1)
      (fun c => bc_le c)
    rw [hw, List.length_append]; omega
  have hWp : w.length < 2 ^ (8 * w.length) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [hdr, ReadNat.natWord_length]; omega
  have h1 : ∀ c ∈ r.circuits, natBitLength c.bottomCount ≤ 8 * w.length := by
    intro c hc
    have h1 := nbl_le_self c.bottomCount
    have h2 := bc_le c
    have h3 := mem_len_le r.circuits (fun c => RepairOrdinary.frame (symWord c)) c hc
    have h4 : (r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))).length ≤ w.length := by
      rw [hw, List.length_append]; omega
    omega
  have h2 : (r.circuits.map (fun c => c.bottomCount + 1)).sum < 2 ^ (8 * w.length) := by omega
  have h3 : (r.circuits.map (fun c => c.bottomCount + 1)).prod < 2 ^ (8 * w.length) := by
    have h1 := prod_le_two_pow r.circuits (fun c => c.bottomCount + 1)
    have h2 : 2 ^ (r.circuits.map (fun c => c.bottomCount + 1)).sum < 2 ^ (8 * w.length) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  exact main_sym r.q L tg r.circuits symWord (fun c => c.bottomCount) (fun c => symWord_pay c) h1 h2 h3 four

theorem main_thr_req (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    MainResult (fields a (.thr r four L tg) 0) r.circuits.length 0 0 := by
  rw [native_thr]
  exact main_thr _ r.q L tg r.circuits.length

/-! ## Cost -/

theorem progCost_le (m V : ℕ) : progCost (8 * m) m V ≤ 5100 * (m + 1) ^ 2 * (V + 1) := by
  unfold progCost mainCost frontCost headerPartCost headerCost symPartCost blockCost bodyCost Setup.cost
  have hV : 1 ≤ V + 1 := by omega
  nlinarith [Nat.zero_le m, Nat.zero_le V, Nat.mul_le_mul hV (le_refl ((m + 1) ^ 2))]

theorem native_le_small (a : DecompositionAlgorithm) (r : Request) :
    (fields a r 0).length + 1 ≤ r.smallSize a := by
  have h1 := field_le_input a r 0
  have h2 := input_le_small a r
  rw [RepairOrdinary.frame_length] at h1
  omega

/-! ## Value bounds -/

theorem len_pos (a : DecompositionAlgorithm) (r : Request) : 1 ≤ (fields a r 0).length := by
  cases r with
  | terminal => rw [native_term]; simp [ReadNat.natWord_length]
  | sym r four L tg => rw [native_sym]; simp [hdr, ReadNat.natWord_length]; omega
  | thr r four L tg => rw [native_thr]; simp [hdr, ReadNat.natWord_length]; omega

theorem len_sym (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) : 5 ≤ (fields a (.sym r four L tg) 0).length := by
  rw [native_sym]; simp [hdr, ReadNat.natWord_length]; omega

theorem len_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) : 5 ≤ (fields a (.thr r four L tg) 0).length := by
  rw [native_thr]; simp [hdr, ReadNat.natWord_length]; omega

theorem sym_bounds (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    (r.circuits.map (fun c => c.bottomCount + 1)).sum ≤ (fields a (.sym r four L tg) 0).length ∧
    (r.circuits.map (fun c => c.bottomCount + 1)).prod ≤ (fields a (.sym r four L tg) 0).length ^ 4 ∧
    (r.circuits.map (fun c => c.bottomCount + 1)).prod < 2 ^ (8 * (fields a (.sym r four L tg) 0).length) := by
  have hpos := len_pos a (.sym r four L tg)
  rw [native_sym] at hpos ⊢
  set w := hdr 0 r.q L tg r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))
    with hw
  have hfl : (r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))).length ≤ w.length := by
    rw [hw, List.length_append]; omega
  have hsum : (r.circuits.map (fun c => c.bottomCount + 1)).sum ≤ w.length := by
    have := sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (symWord c)) (fun c => c.bottomCount + 1)
      (fun c => bc_le c)
    omega
  refine ⟨hsum, ?_, ?_⟩
  · have h1 := prod_le_pow r.circuits (fun c => c.bottomCount + 1) w.length (fun c hc => by
      have := bc_le c
      have := mem_len_le r.circuits (fun c => RepairOrdinary.frame (symWord c)) c hc
      omega)
    exact h1.trans (Nat.pow_le_pow_right hpos four)
  · have h1 := prod_le_two_pow r.circuits (fun c => c.bottomCount + 1)
    have h2 : 2 ^ (r.circuits.map (fun c => c.bottomCount + 1)).sum < 2 ^ (8 * w.length) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem small_lt (m : ℕ) (hm : 1 ≤ m) : m < 2 ^ (8 * m) :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The stages -/

/-- A value emitted from register `v` of the final state is one `UnaryStage`, once every request's run and
value bound are supplied. -/
def nativeStage (a : DecompositionAlgorithm) (v : Fin 26) (val : Request → ℕ)
    (hrun : ∀ r, ∃ σ' : Fin 26 → TS, LRuns (8 * (fields a r 0).length) (prog v)
      (progCost (8 * (fields a r 0).length) (fields a r 0).length (val r)) (initRoles 26 (fields a r 0)) σ' ∧
      σ' 1 = .out (val r))
    (hval : ∀ r, val r + 1 ≤ 5 * ((fields a r 0).length + 1) ^ 4) : UnaryStage a val :=
  scanStage a 0 val (e := 24) (prog v) (fun r => 8 * (fields a r 0).length)
    (fun r => progCost (8 * (fields a r 0).length) (fields a r 0).length (val r)) 25500 6
    (fun r => hrun r)
    (by
      intro r
      have h1 := progCost_le (fields a r 0).length (val r)
      have h2 := hval r
      have h3 := native_le_small a r
      have h4 : ((fields a r 0).length + 1) ^ 6 ≤ (r.smallSize a) ^ 6 := Nat.pow_le_pow_left h3 6
      have e : 5100 * ((fields a r 0).length + 1) ^ 2 * (5 * ((fields a r 0).length + 1) ^ 4) =
          25500 * ((fields a r 0).length + 1) ^ 6 := by ring
      calc progCost (8 * (fields a r 0).length) (fields a r 0).length (val r)
          ≤ 5100 * ((fields a r 0).length + 1) ^ 2 * (val r + 1) := h1
        _ ≤ 5100 * ((fields a r 0).length + 1) ^ 2 * (5 * ((fields a r 0).length + 1) ^ 4) :=
          Nat.mul_le_mul_left _ h2
        _ = 25500 * ((fields a r 0).length + 1) ^ 6 := e
        _ ≤ 25500 * (r.smallSize a) ^ 6 := Nat.mul_le_mul_left _ h4)

/-- **`#circuits`** (`n`, `0` for the terminal sentinel). -/
def circuitsStage (a : DecompositionAlgorithm) : UnaryStage a nCirc :=
  nativeStage a 10 nCirc
    (by
      intro r
      have hW := small_lt _ (len_pos a r)
      cases r with
      | terminal =>
        exact prog_run _ 0 0 0 main_term 10 (by decide) 0 (fun s hn _ _ => by
          show TS.reg s.nc = _
          rw [hn]) (Nat.two_pow_pos _)
      | sym r four L tg =>
        have := len_sym a r four L tg
        exact prog_run _ _ _ _ (main_sym_req a r four L tg) 10 (by decide) r.circuits.length
          (fun s hn _ _ => by
            show TS.reg s.nc = _
            rw [hn]) (by show r.circuits.length < _; omega)
      | thr r four L tg =>
        have := len_thr a r four L tg
        exact prog_run _ _ _ _ (main_thr_req a r four L tg) 10 (by decide) r.circuits.length
          (fun s hn _ _ => by
            show TS.reg s.nc = _
            rw [hn]) (by show r.circuits.length < _; omega))
    (by
      intro r
      have h1 : 1 ≤ ((fields a r 0).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      cases r with
      | terminal => show 0 + 1 ≤ _; omega
      | sym r four L tg => show r.circuits.length + 1 ≤ _; omega
      | thr r four L tg => show r.circuits.length + 1 ≤ _; omega)

/-- **The SYM coordinate sum** `Σ (bottomCount_i + 1)`, `0` off SYM. -/
def symSumStage (a : DecompositionAlgorithm) : UnaryStage a symSumOf :=
  nativeStage a 11 symSumOf
    (by
      intro r
      have hW := small_lt _ (len_pos a r)
      cases r with
      | terminal =>
        exact prog_run _ 0 0 0 main_term 11 (by decide) 0 (fun s _ hs _ => by
          show TS.reg s.sum = _
          rw [hs]) (Nat.two_pow_pos _)
      | sym r four L tg =>
        have hb := sym_bounds a r four L tg
        have e : symSumOf (.sym r four L tg) = (r.circuits.map (fun c => c.bottomCount + 1)).sum :=
          symSum_list r
        rw [e]
        exact prog_run _ _ _ _ (main_sym_req a r four L tg) 11 (by decide) _
          (fun s _ hs _ => by
            show TS.reg s.sum = _
            rw [hs]) (by omega)
      | thr r four L tg =>
        exact prog_run _ _ _ _ (main_thr_req a r four L tg) 11 (by decide) 0
          (fun s _ hs _ => by
            show TS.reg s.sum = _
            rw [hs]) (by omega))
    (by
      intro r
      have h1 : 1 ≤ ((fields a r 0).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      have h2 : (fields a r 0).length + 1 ≤ ((fields a r 0).length + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
      cases r with
      | terminal => show 0 + 1 ≤ _; omega
      | sym r four L tg =>
        have hb := (sym_bounds a r four L tg).1
        have e : symSumOf (.sym r four L tg) = (r.circuits.map (fun c => c.bottomCount + 1)).sum :=
          symSum_list r
        rw [e]; omega
      | thr r four L tg => show 0 + 1 ≤ _; omega)

/-- **`symSel`** (SYM `∏ (bottomCount_i + 1)`, `0` off SYM): RX's `rowsCountStage` input. -/
def symSelStage (a : DecompositionAlgorithm) : UnaryStage a RowsInit.Count.symSelOf :=
  nativeStage a 12 RowsInit.Count.symSelOf
    (by
      intro r
      have hW := small_lt _ (len_pos a r)
      cases r with
      | terminal =>
        exact prog_run _ 0 0 0 main_term 12 (by decide) 0 (fun s _ _ hp => by
          show TS.reg s.prod = _
          rw [hp]) (Nat.two_pow_pos _)
      | sym r four L tg =>
        have hb := sym_bounds a r four L tg
        have e : RowsInit.Count.symSelOf (.sym r four L tg) = (r.circuits.map (fun c => c.bottomCount + 1)).prod :=
          symSel_list r
        rw [e]
        exact prog_run _ _ _ _ (main_sym_req a r four L tg) 12 (by decide) _
          (fun s _ _ hp => by
            show TS.reg s.prod = _
            rw [hp]) hb.2.2
      | thr r four L tg =>
        exact prog_run _ _ _ _ (main_thr_req a r four L tg) 12 (by decide) 0
          (fun s _ _ hp => by
            show TS.reg s.prod = _
            rw [hp]) (by omega))
    (by
      intro r
      have h1 : 1 ≤ ((fields a r 0).length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      cases r with
      | terminal => show 0 + 1 ≤ _; omega
      | sym r four L tg =>
        have hb := (sym_bounds a r four L tg).2.1
        have e : RowsInit.Count.symSelOf (.sym r four L tg) = (r.circuits.map (fun c => c.bottomCount + 1)).prod :=
          symSel_list r
        rw [e]
        have h3 : (fields a (.sym r four L tg) 0).length ^ 4 + 1 ≤ ((fields a (.sym r four L tg) 0).length + 1) ^ 4 := by
          have := Nat.pow_le_pow_left (Nat.le_succ (fields a (.sym r four L tg) 0).length) 4
          nlinarith [Nat.one_le_pow 4 ((fields a (.sym r four L tg) 0).length + 1) (by omega),
            Nat.pow_lt_pow_left (Nat.lt_succ_self (fields a (.sym r four L tg) 0).length) (by norm_num : (4:ℕ) ≠ 0)]
        omega
      | thr r four L tg => show 0 + 1 ≤ _; omega)

end
end NearCubicWires.PacketsKeys.Native


