import Proof.Packets.PacketsCursorChain
import Proof.Packets.PacketsGate
import Proof.Packets.PacketsKeysCoord
import Proof.Packets.PacketsSetupWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.CircBound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.PacketsMeta NearCubicWires.PacketsKeys
open NearCubicWires.PacketsKeys.Native
open NearCubicWires.SupplierPipeline PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.PacketFamilyParent
noncomputable section

def dS : Fin 5 → Fin (3 + 2) := ![0, 1, 3, 2, 4]

theorem dS_inj : Function.Injective dS := by decide

def monusMap2 : UnaryMap2 (fun x y => x - y) where
  extra := 2
  states := _
  machine := RecoveryFocus.machine dS PCPPNativeColdArithmetic.machine
  cost := fun x y => PCPPNativeColdArithmetic.budget x y
  run := by
    intro x y
    have h := Step.of_ready (PCPPNativeColdArithmetic.ready x y)
    have d := h.dock dS dS_inj (fun _ => 0) (unIn2 (3 + 2) x y) (fun _ => rfl) (by
      intro j; fin_cases j <;> rfl)
    rw [dockH_zero] at d
    refine ⟨_, _, d, ?_, ?_⟩
    · rw [show (⟨2, by omega⟩ : Fin (3 + 2)) = dS 3 from rfl, install_slot _ dS_inj]
      rfl
    · rfl

theorem monus_cost (x y : ℕ) : monusMap2.cost x y ≤ 6 * (x + y + 3) ^ 1 := by
  change 2 * max x y + 4 ≤ _
  rw [pow_one]
  omega

/-! ## 2. Constants -/

/-- The machine that halts at once (2 tapes). -/
def halt2 : Machine 2 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

/-- The value `0`. -/
def zeroS (a : DecompositionAlgorithm) : UnaryStage a (fun _ => 0) where
  extra := 0
  states := 1
  machine := halt2
  cost := fun _ => 0
  coefficient := 0
  degree := 0
  cost_le := fun _ => Nat.zero_le _
  run := by
    intro r
    exact ⟨fun _ => 0, inBank (2 + 0) (Request.input a r),
      ⟨_, runFrom_zero_of_halted halt2 _ rfl, rfl, rfl, le_refl 0⟩, rfl, rfl, rfl, rfl⟩

/-- A constant. -/
def constS (a : DecompositionAlgorithm) (c : ℕ) : UnaryStage a (fun _ => c) :=
  ((zeroS a).thenMapP (plusMap c) (2 * c + 4) 1 (plus_cost c)).ofEq (fun _ => by simp)

/-! ## 3. THR prefix sums (input part 5): PK's `prog2` truncated after `j` blocks -/

/-- Setup, then the first `j` THR blocks. -/
def pre2 : ℕ → (s : ℕ) × Machine 26 s
  | 0 => ⟨_, setupD⟩
  | j + 1 => ⟨_, Composition.machine (pre2 j).2 (block2 ⟨min j 3, by omega⟩)⟩

def pre2Cost (W m : ℕ) : ℕ → ℕ
  | 0 => Setup.cost 8 m
  | j + 1 => pre2Cost W m j + 1 + block2Cost W m

theorem pre2_run {α : Type} (L : List α) (pay : α → List Bool) (n1 n2 : α → ℕ)
    (hpay : ∀ a, ∃ rest, pay a = natWord (n1 a) ++ natWord (n2 a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (n1 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length ∧
      natBitLength (n2 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
    (hsumB : (L.map n2).sum < 2 ^ (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)) :
    ∀ j, j ≤ 4 → ∃ bb, LRuns (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length) (pre2 j).2
      (pre2Cost (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
        (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length j)
      (initRoles 26 (L.flatMap (fun a => RepairOrdinary.frame (pay a))))
      (nv (L.flatMap (fun a => RepairOrdinary.frame (pay a)))
        (chain2 (s0 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) L (fun a => RepairOrdinary.frame (pay a))
          n2 j bb))
  | 0, _ => ⟨0, setup_run _⟩
  | j + 1, hj => by
    obtain ⟨bb, h⟩ := pre2_run L pay n1 n2 hpay hnb hsumB j (by omega)
    obtain ⟨bb', hb⟩ := block2_step (W := 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
      (L.flatMap (fun a => RepairOrdinary.frame (pay a))) L pay n1 n2 rfl hpay hnb hsumB
      (s0 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) ⟨min j 3, by omega⟩ bb _ le_rfl
    have e : min j 3 = j := by omega
    have hb' := (congrArg (fun x => LRuns (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
      (block2 ⟨min j 3, by omega⟩)
      (block2Cost (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
        (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
      (nv (L.flatMap (fun a => RepairOrdinary.frame (pay a)))
        (chain2 (s0 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) L (fun a => RepairOrdinary.frame (pay a))
          n2 x bb))
      (nv (L.flatMap (fun a => RepairOrdinary.frame (pay a)))
        (chain2 (s0 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) L (fun a => RepairOrdinary.frame (pay a))
          n2 (x + 1) bb'))) e).mp hb
    exact ⟨bb', h.seq hb'⟩

/-- The THR prefix program: `pre2 j`, then emit the `sum` register. -/
def progT (j : ℕ) := Composition.machine (pre2 j).2 (RecoveryFocus.machine ![(4 : Fin 26), 7, 11, 6, 1] Emit.machine)

def progTCost (W m j V : ℕ) : ℕ := pre2Cost W m j + 1 + (V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)

theorem progT_run {α : Type} (L : List α) (pay : α → List Bool) (n1 n2 : α → ℕ)
    (hpay : ∀ a, ∃ rest, pay a = natWord (n1 a) ++ natWord (n2 a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (n1 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length ∧
      natBitLength (n2 a) ≤ 8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
    (hsum : (L.map n2).sum ≤ (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length) (j : ℕ) (hj : j ≤ 4) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length) (progT j)
      (progTCost (8 * (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
        (L.flatMap (fun a => RepairOrdinary.frame (pay a))).length j ((L.take j).map n2).sum)
      (initRoles 26 (L.flatMap (fun a => RepairOrdinary.frame (pay a)))) σ' ∧ σ' 1 = .out ((L.take j).map n2).sum := by
  set w := L.flatMap (fun a => RepairOrdinary.frame (pay a)) with hw
  have hsumB : (L.map n2).sum < 2 ^ (8 * w.length) := lt_pow8 _ _ hsum
  obtain ⟨bb, h⟩ := pre2_run L pay n1 n2 hpay hnb hsumB j hj
  have hle := sum_take_le L n2 j
  have e5 := emitAt (W := 8 * w.length) w (chain2 (s0 w) L (fun a => RepairOrdinary.frame (pay a)) n2 j bb) 11
    (by decide) ((L.take j).map n2).sum rfl (by omega)
  refine ⟨_, h.seq e5, ?_⟩
  simp [chain2, s0]

/-- The THR prefix sum of the first `j` child counts (`0` off THR). -/
def thrPre (a : DecompositionAlgorithm) (j : ℕ) : Request → ℕ
  | .thr r _ _ _ => ((r.circuits.take j).map (fun c => (ThresholdRows.children a c).length)).sum
  | _ => 0

theorem thrPre_run_req (a : DecompositionAlgorithm) (j : ℕ) (hj : j ≤ 4) (r : Request) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * (fields a r 4).length) (progT j)
      (progTCost (8 * (fields a r 4).length) (fields a r 4).length j (thrPre a j r))
      (initRoles 26 (fields a r 4)) σ' ∧ σ' 1 = .out (thrPre a j r) := by
  cases r with
  | thr r four L tg =>
    rw [top_thr]
    have hsum : (r.circuits.map (fun c => (ThresholdRows.children a c).length)).sum ≤
        (r.circuits.flatMap (fun c => RepairOrdinary.frame (tpay a c))).length :=
      sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (tpay a c)) _ (fun c => tpay_ch a c)
    refine progT_run r.circuits (tpay a) (fun c => c.top.support.card) (fun c => (ThresholdRows.children a c).length)
      (fun c => ⟨_, tpay_split a c⟩) ?_ hsum j hj
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
    have h := progT_run ([] : List ℕ) (fun _ => natWord 0 ++ natWord 0) (fun _ => 0) (fun _ => 0)
      (fun _ => ⟨[], by simp⟩) (fun _ h => by simp at h) (by simp) j hj
    simpa [thrPre] using h
  | sym r four L tg =>
    rw [top_fields a (.sym r four L tg) (fun _ _ _ _ h => by cases h)]
    have h := progT_run ([] : List ℕ) (fun _ => natWord 0 ++ natWord 0) (fun _ => 0) (fun _ => 0)
      (fun _ => ⟨[], by simp⟩) (fun _ h => by simp at h) (by simp) j hj
    simpa [thrPre] using h

theorem pre2Cost_le (W m j : ℕ) (hj : j ≤ 4) : pre2Cost W m j ≤ pre2Cost W m 4 := by
  interval_cases j <;> simp only [pre2Cost] <;> omega

theorem progTCost_le (m j V : ℕ) (hj : j ≤ 4) : progTCost (8 * m) m j V ≤ 5100 * (m + 1) ^ 2 * (V + 1) := by
  have h1 := pre2Cost_le (8 * m) m j hj
  have h2 := prog2Cost_le m V
  have e : prog2Cost (8 * m) m V = pre2Cost (8 * m) m 4 + 1 +
      (V + 1) * ((2 * (8 * m) + 3) + (2 * (8 * m) + 3 + 1 + 1) + 2) := by
    simp only [prog2Cost, pre2Cost]; omega
  unfold progTCost
  omega

theorem thrPre_le (a : DecompositionAlgorithm) (j : ℕ) (r : Request) : thrPre a j r ≤ (fields a r 4).length := by
  have h := thrSum_le a r
  cases r with
  | thr r four L tg =>
    have h2 := sum_take_le r.circuits (fun c => (ThresholdRows.children a c).length) j
    have e : thrSumOf a (.thr r four L tg) = (r.circuits.map (fun c => (ThresholdRows.children a c).length)).sum :=
      thrSum_list a r
    show ((r.circuits.take j).map (fun c => (ThresholdRows.children a c).length)).sum ≤ _
    omega
  | terminal => exact Nat.zero_le _
  | sym r four L tg => exact Nat.zero_le _

/-- **THR prefix sums** as stages. -/
def thrPreStage (a : DecompositionAlgorithm) (j : ℕ) (hj : j ≤ 4) : UnaryStage a (thrPre a j) :=
  scanStage a 4 (thrPre a j) (e := 24) (progT j) (fun r => 8 * (fields a r 4).length)
    (fun r => progTCost (8 * (fields a r 4).length) (fields a r 4).length j (thrPre a j r)) 5100 3
    (fun r => thrPre_run_req a j hj r)
    (by
      intro r
      have h1 := progTCost_le (fields a r 4).length j (thrPre a j r) hj
      have h2 := thrPre_le a j r
      have h3 := top_le_small a r
      have h4 : ((fields a r 4).length + 1) ^ 3 ≤ (r.smallSize a) ^ 3 := Nat.pow_le_pow_left h3 3
      have e : ((fields a r 4).length + 1) ^ 3 = ((fields a r 4).length + 1) ^ 2 * ((fields a r 4).length + 1) := by
        ring
      calc progTCost (8 * (fields a r 4).length) (fields a r 4).length j (thrPre a j r)
          ≤ 5100 * ((fields a r 4).length + 1) ^ 2 * (thrPre a j r + 1) := h1
        _ ≤ 5100 * ((fields a r 4).length + 1) ^ 2 * ((fields a r 4).length + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 5100 * ((fields a r 4).length + 1) ^ 3 := by rw [e]; ring
        _ ≤ 5100 * (r.smallSize a) ^ 3 := Nat.mul_le_mul_left _ h4)

/-! ## 4. SYM prefix sums (input part 1): PK's `main` with its circuit blocks truncated after `j` -/

/-- The product increment, then the first `j` SYM blocks. -/
def symPartJ : ℕ → (s : ℕ) × Machine 26 s
  | 0 => ⟨_, swAt addF true true (4 : Fin 26) 12 7 6⟩
  | j + 1 => ⟨_, Composition.machine (symPartJ j).2 (block ⟨min j 3, by omega⟩)⟩

def symPartJCost (W m : ℕ) : ℕ → ℕ
  | 0 => 2 * W + 3
  | j + 1 => symPartJCost W m j + 1 + blockCost W m

theorem symPartJ_run {α : Type} {W : ℕ} (w pre : List Bool) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hw : w = pre ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)))
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ W) (hW1 : 1 ≤ W)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ W) (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ W)
    (S : NS) (hsp : S.sp = 1 + pre.length) (hsum : S.sum = 0) (hprod : S.prod = 0) (hct : S.ct = ctAfter 0) :
    ∀ j, j ≤ 4 → ∃ bb pp, LRuns W (symPartJ j).2 (symPartJCost W w.length j) (nv w S)
      (nv w (chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) j bb pp))
  | 0, _ => by
    have e0 := incProd (W := W) w S (by
      rw [hprod]
      have : 2 ^ 0 < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
      simpa using this)
    have hs0 : ({ S with prod := S.prod + 1, fl := false } : NS) =
        chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) 0 S.b S.p2 := by
      cases S
      simp only [chainSt] at hsp hsum hprod hct ⊢
      subst hsp hsum hprod hct
      simp
    rw [hs0] at e0
    exact ⟨S.b, S.p2, e0⟩
  | j + 1, hj => by
    obtain ⟨bb, pp, h⟩ := symPartJ_run w pre L pay num hw hpay hnb hW1 hsumB hprodB S hsp hsum hprod hct j (by omega)
    obtain ⟨bb', pp', hb⟩ := block_step (W := W) w pre L pay num hw hpay hnb hW1 hsumB hprodB S ⟨min j 3, by omega⟩
      bb pp w.length le_rfl
    have e : min j 3 = j := by omega
    have hb' := (congrArg (fun x => LRuns W (block ⟨min j 3, by omega⟩) (blockCost W w.length)
      (nv w (chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) x bb pp))
      (nv w (chainSt S pre L (fun a => RepairOrdinary.frame (pay a)) (fun a => num a + 1) (x + 1) bb' pp'))) e).mp hb
    exact ⟨bb', pp', h.seq hb'⟩

/-- PK's `main` with `symPartJ j` in place of the four blocks. -/
def mainJ (j : ℕ) := Ite front (Ite header (symPartJ j).2 (nop 26) (6 : Fin 26)) (nop 26) (6 : Fin 26)

def mainJCost (W m j : ℕ) : ℕ := frontCost W m + (headerCost W + symPartJCost W m j + 0 + 2) + 0 + 2

def MainJ (w : List Bool) (j sm : ℕ) : Prop :=
  ∃ s : NS, LRuns (8 * w.length) (mainJ j) (mainJCost (8 * w.length) w.length j) (initRoles 26 w) (nv w s) ∧
    s.out = 0 ∧ s.sum = sm

theorem mainJ_term (j : ℕ) : MainJ (natWord 2) j 0 := by
  refine ⟨sF (natWord 2) 2, ?_, rfl, rfl⟩
  unfold mainJ mainJCost
  exact Ite.runs (W := 8 * (natWord 2).length)
    (np := headerCost (8 * (natWord 2).length) + symPartJCost (8 * (natWord 2).length) (natWord 2).length j + 0 + 2)
    (nq := 0) _ _ _ (6 : Fin 26) false (front_run (natWord 2) [] 2 (by simp) le_rfl (by simp))
    (by rfl) (fun h => by simp at h) (fun _ => nop_lruns _)

theorem mainJ_thr (j : ℕ) (rest : List Bool) (q L tg n : ℕ) : MainJ (hdr 1 q L tg n ++ rest) j 0 := by
  set w := hdr 1 q L tg n ++ rest with hw
  refine ⟨sH w 1 q L tg n, ?_, rfl, rfl⟩
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [Native.hdr]; omega
  unfold mainJ mainJCost
  refine Ite.runs (W := 8 * w.length)
    (np := headerCost (8 * w.length) + symPartJCost (8 * w.length) w.length j + 0 + 2) (nq := 0) _ _ _ (6 : Fin 26)
    true (front_run w (natWord q ++ natWord L ++ natWord tg ++ natWord n ++ rest) 1 (by simp [hw, Native.hdr]) (by omega) hW1)
    (by rfl) (fun _ => ?_) (fun h => by simp at h)
  exact Ite.runs (W := 8 * w.length) (np := symPartJCost (8 * w.length) w.length j) (nq := 0) _ _ _ (6 : Fin 26) false
    (header_run w rest 1 q L tg n rfl (by omega)) (by rfl) (fun h => by simp at h) (fun _ => nop_lruns _)

theorem mainJ_sym {α : Type} (q Lv tg : ℕ) (L : List α) (pay : α → List Bool) (num : α → ℕ)
    (hpay : ∀ a, ∃ rest, pay a = natWord (num a) ++ rest)
    (hnb : ∀ a ∈ L, natBitLength (num a) ≤ 8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length)
    (hsumB : (L.map (fun a => num a + 1)).sum < 2 ^ (8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length))
    (hprodB : (L.map (fun a => num a + 1)).prod < 2 ^ (8 * (hdr 0 q Lv tg L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))).length))
    (j : ℕ) (hj : j ≤ 4) :
    MainJ (hdr 0 q Lv tg L.length ++ L.flatMap (fun a => RepairOrdinary.frame (pay a))) j
      ((L.take j).map (fun a => num a + 1)).sum := by
  set w := hdr 0 q Lv tg L.length ++ L.flatMap (fun a => RepairOrdinary.frame (pay a)) with hw
  have hW1 : 1 ≤ w.length := by rw [hw]; simp [Native.hdr]; omega
  obtain ⟨bb, pp, hsp⟩ := symPartJ_run (W := 8 * w.length) w (hdr 0 q Lv tg L.length) L pay num hw hpay hnb
    (by omega) hsumB hprodB (sH w 0 q Lv tg L.length) rfl rfl rfl rfl j hj
  refine ⟨chainSt (sH w 0 q Lv tg L.length) (hdr 0 q Lv tg L.length) L (fun a => RepairOrdinary.frame (pay a))
    (fun a => num a + 1) j bb pp, ?_, rfl, rfl⟩
  unfold mainJ mainJCost
  refine Ite.runs (W := 8 * w.length)
    (np := headerCost (8 * w.length) + symPartJCost (8 * w.length) w.length j + 0 + 2) (nq := 0) _ _ _ (6 : Fin 26)
    true (front_run w (natWord q ++ natWord Lv ++ natWord tg ++ natWord L.length ++
      L.flatMap (fun a => RepairOrdinary.frame (pay a))) 0 (by simp [hw, Native.hdr]) (by omega) hW1)
    (by rfl) (fun _ => ?_) (fun h => by simp at h)
  exact Ite.runs (W := 8 * w.length) (np := symPartJCost (8 * w.length) w.length j) (nq := 0) _ _ _ (6 : Fin 26) true
    (header_run w _ 0 q Lv tg L.length rfl (by omega)) (by rfl) (fun _ => hsp) (fun h => by simp at h)

/-- The SYM prefix program: `mainJ j`, then emit the `sum` register. -/
def progS (j : ℕ) := Composition.machine (mainJ j) (RecoveryFocus.machine ![(4 : Fin 26), 7, 11, 6, 1] Emit.machine)

def progSCost (W m j V : ℕ) : ℕ := mainJCost W m j + 1 + (V + 1) * ((2 * W + 3) + (2 * W + 3 + 1 + 1) + 2)

theorem progS_run (w : List Bool) (j sm : ℕ) (h : MainJ w j sm) (hVW : sm < 2 ^ (8 * w.length)) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * w.length) (progS j) (progSCost (8 * w.length) w.length j sm) (initRoles 26 w) σ' ∧
      σ' 1 = .out sm := by
  obtain ⟨s, hm, ho, hs⟩ := h
  have he := emitAt (W := 8 * w.length) w s 11 (by decide) sm (by show TS.reg s.sum = _; rw [hs]) hVW
  refine ⟨_, hm.seq he, ?_⟩
  simp [ho]

/-- The SYM prefix sum of the first `j` values `bottomCount + 1` (`0` off SYM). -/
def symPre (j : ℕ) : Request → ℕ
  | .sym r _ _ _ => ((r.circuits.take j).map (fun c => c.bottomCount + 1)).sum
  | _ => 0

theorem symPre_le (a : DecompositionAlgorithm) (j : ℕ) (r : Request) : symPre j r ≤ (fields a r 0).length := by
  cases r with
  | sym r four L tg =>
    have h1 := (sym_bounds a r four L tg).1
    have h2 := sum_take_le r.circuits (fun c => c.bottomCount + 1) j
    show ((r.circuits.take j).map (fun c => c.bottomCount + 1)).sum ≤ _
    omega
  | terminal => exact Nat.zero_le _
  | thr r four L tg => exact Nat.zero_le _

theorem symPre_run_req (a : DecompositionAlgorithm) (j : ℕ) (hj : j ≤ 4) (r : Request) :
    ∃ σ' : Fin 26 → TS, LRuns (8 * (fields a r 0).length) (progS j)
      (progSCost (8 * (fields a r 0).length) (fields a r 0).length j (symPre j r))
      (initRoles 26 (fields a r 0)) σ' ∧ σ' 1 = .out (symPre j r) := by
  have hW := small_lt _ (len_pos a r)
  have hle := symPre_le a j r
  refine progS_run _ j _ ?_ (by omega)
  cases r with
  | terminal => exact mainJ_term j
  | thr r four L tg => rw [native_thr]; exact mainJ_thr j _ r.q L tg r.circuits.length
  | sym r four L tg =>
    have hl := len_sym a r four L tg
    rw [native_sym] at hl ⊢
    set w := Native.hdr 0 r.q L tg r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))
      with hw
    have hsum : (r.circuits.map (fun c => c.bottomCount + 1)).sum ≤ w.length := by
      have := sum_le_flatMap r.circuits (fun c => RepairOrdinary.frame (symWord c)) (fun c => c.bottomCount + 1)
        (fun c => bc_le c)
      rw [hw, List.length_append]; omega
    have hWp : w.length < 2 ^ (8 * w.length) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
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
    exact mainJ_sym r.q L tg r.circuits symWord (fun c => c.bottomCount) (fun c => symWord_pay c) h1 h2 h3 j hj

theorem symPartJCost_le (W m j : ℕ) (hj : j ≤ 4) : symPartJCost W m j ≤ symPartCost W m := by
  interval_cases j <;> simp only [symPartJCost, symPartCost] <;> omega

theorem progSCost_le (m j V : ℕ) (hj : j ≤ 4) : progSCost (8 * m) m j V ≤ 5100 * (m + 1) ^ 2 * (V + 1) := by
  have h1 := symPartJCost_le (8 * m) m j hj
  have h2 := progCost_le m V
  unfold progSCost mainJCost
  unfold progCost mainCost headerPartCost at h2
  omega

/-- **SYM prefix sums** as stages. -/
def symPreStage (a : DecompositionAlgorithm) (j : ℕ) (hj : j ≤ 4) : UnaryStage a (symPre j) :=
  scanStage a 0 (symPre j) (e := 24) (progS j) (fun r => 8 * (fields a r 0).length)
    (fun r => progSCost (8 * (fields a r 0).length) (fields a r 0).length j (symPre j r)) 5100 3
    (fun r => symPre_run_req a j hj r)
    (by
      intro r
      have h1 := progSCost_le (fields a r 0).length j (symPre j r) hj
      have h2 := symPre_le a j r
      have h3 := native_le_small a r
      have h4 : ((fields a r 0).length + 1) ^ 3 ≤ (r.smallSize a) ^ 3 := Nat.pow_le_pow_left h3 3
      have e : ((fields a r 0).length + 1) ^ 3 = ((fields a r 0).length + 1) ^ 2 * ((fields a r 0).length + 1) := by
        ring
      calc progSCost (8 * (fields a r 0).length) (fields a r 0).length j (symPre j r)
          ≤ 5100 * ((fields a r 0).length + 1) ^ 2 * (symPre j r + 1) := h1
        _ ≤ 5100 * ((fields a r 0).length + 1) ^ 2 * ((fields a r 0).length + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = 5100 * ((fields a r 0).length + 1) ^ 3 := by rw [e]; ring
        _ ≤ 5100 * (r.smallSize a) ^ 3 := Nat.mul_le_mul_left _ h4)

/-! ## 5. `circBound` -/

/-- The prefix sums of both kinds (each is `0` off its kind). -/
def preSum (a : DecompositionAlgorithm) (j : ℕ) (r : Request) : ℕ := symPre j r + thrPre a j r

def preStage (a : DecompositionAlgorithm) (j : ℕ) (hj : j ≤ 4) : UnaryStage a (preSum a j) :=
  (symPreStage a j hj).pairP (thrPreStage a j hj) addMap2 6 1 add_cost

theorem take_succ_sum {α : Type} (L : List α) (g : α → ℕ) (i : ℕ) :
    ((L.take (i + 1)).map g).sum - ((L.take i).map g).sum = if h : i < L.length then g L[i] else 0 := by
  by_cases h : i < L.length
  · have e : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem h
    rw [dif_pos h, e, List.map_append, List.sum_append]
    simp
  · rw [dif_neg h, List.take_of_length_le (show L.length ≤ i + 1 by omega), List.take_of_length_le (by omega)]
    simp

/-- **The value identity**: the prefix-sum difference plus the past-the-end indicator is `circBound`. -/
theorem circBound_eq (a : DecompositionAlgorithm) (i : ℕ) (r : Request) :
    (preSum a (i + 1) r - preSum a i r) + (if nCirc r - i = 0 then 1 else 0) =
      PacketsGlue.CursorChain.circBound a i r := by
  cases r with
  | terminal => simp [preSum, symPre, thrPre, nCirc, PacketsGlue.CursorChain.circBound]
  | sym r four L tg =>
    have e := take_succ_sum r.circuits (fun c => c.bottomCount + 1) i
    simp only [preSum, symPre, thrPre, nCirc, PacketsGlue.CursorChain.circBound, Nat.add_zero]
    rw [e]
    by_cases h : i < r.circuits.length
    · rw [dif_pos h, dif_pos h, if_neg (by omega)]
      simp [List.get_eq_getElem]
    · rw [dif_neg h, dif_neg h, if_pos (by omega)]
  | thr r four L tg =>
    have e := take_succ_sum r.circuits (fun c => (ThresholdRows.children a c).length) i
    simp only [preSum, symPre, thrPre, nCirc, PacketsGlue.CursorChain.circBound, Nat.zero_add]
    rw [e]
    by_cases h : i < r.circuits.length
    · rw [dif_pos h, dif_pos h, if_neg (by omega)]
      simp [List.get_eq_getElem]
    · rw [dif_neg h, dif_neg h, if_pos (by omega)]

def diffStage (a : DecompositionAlgorithm) (i : ℕ) (hi : i < 4) :
    UnaryStage a (fun r => preSum a (i + 1) r - preSum a i r) :=
  (preStage a (i + 1) (by omega)).pairP (preStage a i (by omega)) monusMap2 6 1 monus_cost

def indStage (a : DecompositionAlgorithm) (i : ℕ) : UnaryStage a (fun r => if nCirc r - i = 0 then 1 else 0) :=
  ((circuitsStage a).pairP (constS a i) monusMap2 6 1 monus_cost).thenMapP isZeroMap 4 1
    (fun _ => by change 2 * 1 + 2 ≤ _; rw [pow_one]; omega)

def circBoundStage (a : DecompositionAlgorithm) (i : Fin 4) :
    UnaryStage a (PacketsGlue.CursorChain.circBound a i.val) :=
  ((diffStage a i.val i.isLt).pairP (indStage a i.val) addMap2 6 1 add_cost).ofEq (fun r => circBound_eq a i.val r)

end
end NearCubicWires.PacketsConstruction.CircBound
