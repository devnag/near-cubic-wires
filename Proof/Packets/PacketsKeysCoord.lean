import Proof.Packets.PacketsKeysTopSum

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

/-! ## The program on input part 5 -/

def prog2 :=
  Composition.machine setupD
    (Composition.machine (block2 0) (Composition.machine (block2 1) (Composition.machine (block2 2)
      (Composition.machine (block2 3) (RecoveryFocus.machine ![(4 : Fin 26), 7, 11, 6, 1] Emit.machine)))))

def prog2Cost (W m V : ℕ) : ℕ :=
  Setup.cost 8 m + 1 + (block2Cost W m + 1 + (block2Cost W m + 1 + (block2Cost W m + 1 +
    (block2Cost W m + 1 + (V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)))))

theorem lt_pow8 (x m : ℕ) (h : x ≤ m) : x < 2 ^ (8 * m) :=
  lt_of_le_of_lt h (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem top_run {α : Type} (L : List α) (pay : α → List Bool) (n1 n2 : α → ℕ)
    (hpay : ∀ a, ∃ rest, pay a = natWord (n1 a) ++ natWord (n2 a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (n1 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length ∧
      natBitLength (n2 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
    (hsum : (L.map n2).sum ≤ (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length) (hL : L.length ≤ 4) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length) prog2
      (prog2Cost (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
        (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length (L.map n2).sum)
      (initRoles 26 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) σ' ∧ σ' 1 = .out (L.map n2).sum := by
  set w := L.flatMap (fun a => RepairOrdinary.frame (pay a)) with hw
  have hsumB : (L.map n2).sum < 2 ^ (8 * w.length) := lt_pow8 _ _ hsum
  have e0 := setup_run w
  have hs0 : nv w (s0 w) = nv w (chain2 (s0 w) L (fun a => RepairOrdinary.frame (pay a)) n2 0 0) := rfl
  rw [hs0] at e0
  obtain ⟨b1, e1⟩ := block2_step (W := 8 * w.length) w L pay n1 n2 hw hpay hnb hsumB (s0 w) 0 0 _ le_rfl
  obtain ⟨b2, e2⟩ := block2_step (W := 8 * w.length) w L pay n1 n2 hw hpay hnb hsumB (s0 w) 1 b1 _ le_rfl
  obtain ⟨b3, e3⟩ := block2_step (W := 8 * w.length) w L pay n1 n2 hw hpay hnb hsumB (s0 w) 2 b2 _ le_rfl
  obtain ⟨b4, e4⟩ := block2_step (W := 8 * w.length) w L pay n1 n2 hw hpay hnb hsumB (s0 w) 3 b3 _ le_rfl
  have htake : L.take 4 = L := List.take_of_length_le hL
  have e5 := emitAt (W := 8 * w.length) w (chain2 (s0 w) L (fun a => RepairOrdinary.frame (pay a)) n2 (3 + 1) b4) 11
    (by decide) (L.map n2).sum (by show TS.reg (((L.take (3 + 1)).map n2).sum) = _; rw [htake]) hsumB
  refine ⟨_, e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))), ?_⟩
  simp [chain2, s0]

/-! ## The THR sum, per request -/

/-- `Σ |children_i|` on THR, `0` otherwise (input part 5 is empty off THR). -/
def thrSumOf (a : DecompositionAlgorithm) : Request → ℕ
  | .thr r _ _ _ => ∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length
  | _ => 0

theorem thrSum_list (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    ∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length =
      (r.circuits.map (fun c => (ThresholdRows.children a c).length)).sum := by
  simp only [List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem r.circuits (fun c => (ThresholdRows.children a c).length)

theorem coordSum_eq (a : DecompositionAlgorithm) (r : Request) : coordSum a r = symSumOf r + thrSumOf a r := by
  cases r <;> simp [coordSum, symSumOf, thrSumOf]

theorem exactWord_pos {n : ℕ} (g : ExactThresholdGate n) : 1 ≤ (exactWord g).length := by
  simp only [exactWord, List.length_append, intWord, List.length_cons]
  omega

/-- The THR payload of one circuit. -/
def tpay (a : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)

theorem tpay_split (a : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    tpay a c = natWord c.top.support.card ++ natWord (ThresholdRows.children a c).length ++
      (ThresholdRows.children a c).flatMap exactWord := by
  simp [tpay, exactListWord, List.append_assoc]

theorem tpay_ch (a : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :
    (ThresholdRows.children a c).length ≤ (RepairOrdinary.frame (tpay a c)).length := by
  have h := len_le_flatMap (ThresholdRows.children a c) exactWord exactWord_pos
  rw [RepairOrdinary.frame_length, tpay_split]
  simp only [List.length_append]
  omega

theorem top_fields (a : DecompositionAlgorithm) (r : Request) (hr : ∀ r' four L tg, r ≠ .thr r' four L tg) :
    fields a r 4 = ([] : List ℕ).flatMap (fun _ => RepairOrdinary.frame (natWord 0 ++ natWord 0)) := by
  cases r with
  | terminal => rfl
  | sym r four L tg => rfl
  | thr r four L tg => exact absurd rfl (hr r four L tg)

theorem top_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L tg : ℕ) :
    fields a (.thr r four L tg) 4 = r.circuits.flatMap (fun c => RepairOrdinary.frame (tpay a c)) := rfl

theorem top_run_req (a : DecompositionAlgorithm) (r : Request) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * (fields a r 4).length) prog2
      (prog2Cost (8 * (fields a r 4).length) (fields a r 4).length (thrSumOf a r))
      (initRoles 26 (fields a r 4)) σ' ∧ σ' 1 = .out (thrSumOf a r) := by
  cases r with
  | thr r four L tg =>
    rw [top_thr]
    have e : thrSumOf a (.thr r four L tg) = (r.circuits.map (fun c => (ThresholdRows.children a c).length)).sum :=
      thrSum_list a r
    rw [e]
    have hsum : (r.circuits.map (fun c => (ThresholdRows.children a c).length)).sum ≤
        (r.circuits.flatMap (fun c => RepairOrdinary.frame (tpay a c))).length :=
      sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (tpay a c)) _ (fun c => tpay_ch a c)
    refine top_run r.circuits (tpay a) (fun c => c.top.support.card) (fun c => (ThresholdRows.children a c).length)
      (fun c => ⟨_, tpay_split a c⟩) ?_ hsum four
    intro c hc
    have h3 := mem_len_le r.circuits (fun c => RepairOrdinary.frame (tpay a c)) c hc
    have h4 : (tpay a c).length ≤ (RepairOrdinary.frame (tpay a c)).length := by
      rw [RepairOrdinary.frame_length]; omega
    have h5 := nbl_le c.top.support.card
    have h6 := nbl_le (ThresholdRows.children a c).length
    have h7 : (natWord c.top.support.card).length + (natWord (ThresholdRows.children a c).length).length ≤
        (tpay a c).length := by
      rw [tpay_split]; simp only [List.length_append]; omega
    constructor <;> omega
  | terminal =>
    rw [top_fields a .terminal (fun _ _ _ _ h => by cases h)]
    exact top_run [] (fun _ => natWord 0 ++ natWord 0) (fun _ => 0) (fun _ => 0)
      (fun _ => ⟨[], by simp⟩) (fun _ h => by simp at h) (by simp) (by simp)
  | sym r four L tg =>
    rw [top_fields a (.sym r four L tg) (fun _ _ _ _ h => by cases h)]
    exact top_run [] (fun _ => natWord 0 ++ natWord 0) (fun _ => 0) (fun _ => 0)
      (fun _ => ⟨[], by simp⟩) (fun _ h => by simp at h) (by simp) (by simp)

/-! ## The stages -/

theorem prog2Cost_le (m V : ℕ) : prog2Cost (8 * m) m V ≤ 5100 * (m + 1) ^ 2 * (V + 1) := by
  unfold prog2Cost block2Cost body2Cost Setup.cost
  have hV : 1 ≤ V + 1 := by omega
  nlinarith [Nat.zero_le m, Nat.zero_le V, Nat.mul_le_mul hV (le_refl ((m + 1) ^ 2))]

theorem top_le_small (a : DecompositionAlgorithm) (r : Request) : (fields a r 4).length + 1 ≤ r.smallSize a := by
  have h1 := field_le_input a r 4
  have h2 := input_le_small a r
  rw [RepairOrdinary.frame_length] at h1
  omega

theorem thrSum_le (a : DecompositionAlgorithm) (r : Request) : thrSumOf a r ≤ (fields a r 4).length := by
  cases r with
  | thr r four L tg =>
    rw [top_thr]
    show ∑ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length ≤ _
    rw [thrSum_list]
    exact sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (tpay a c)) _ (fun c => tpay_ch a c)
  | terminal => exact Nat.zero_le _
  | sym r four L tg => exact Nat.zero_le _

/-- **The THR coordinate sum** `Σ |children_i|` (`0` off THR). -/
def topSumStage (a : DecompositionAlgorithm) : UnaryStage a (thrSumOf a) :=
  scanStage a 4 (thrSumOf a) (e := 24) prog2 (fun r => 8 * (fields a r 4).length)
    (fun r => prog2Cost (8 * (fields a r 4).length) (fields a r 4).length (thrSumOf a r)) 5100 3
    (fun r => top_run_req a r)
    (by
      intro r
      have h1 := prog2Cost_le (fields a r 4).length (thrSumOf a r)
      have h2 := thrSum_le a r
      have h3 := top_le_small a r
      have h4 : ((fields a r 4).length + 1) ^ 3 ≤ (r.smallSize a) ^ 3 := Nat.pow_le_pow_left h3 3
      have e : ((fields a r 4).length + 1) ^ 3 = ((fields a r 4).length + 1) ^ 2 * ((fields a r 4).length + 1) := by
        ring
      calc prog2Cost (8 * (fields a r 4).length) (fields a r 4).length (thrSumOf a r)
          ≤ 5100 * ((fields a r 4).length + 1) ^ 2 * (thrSumOf a r + 1) := h1
        _ ≤ 5100 * ((fields a r 4).length + 1) ^ 2 * ((fields a r 4).length + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 5100 * ((fields a r 4).length + 1) ^ 3 := by rw [e]; ring
        _ ≤ 5100 * (r.smallSize a) ^ 3 := Nat.mul_le_mul_left _ h4)

/-- **`coordS`**: PG's `fieldWidthStage` input. -/
def coordStage (a : DecompositionAlgorithm) : UnaryStage a (coordSum a) := by
  have h : coordSum a = fun r => symSumOf r + thrSumOf a r := funext (coordSum_eq a)
  rw [h]
  exact (symSumStage a).pairP (topSumStage a) addMap2 6 1 add_cost

end
end NearCubicWires.PacketsKeys.Native

