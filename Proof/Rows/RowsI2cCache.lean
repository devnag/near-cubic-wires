import Proof.Rows.RowsI2cVecProg
import Proof.Rows.RowsI2cPool
import Proof.Rows.RowsI2cStreamStage
import Proof.Rows.RowsI2cPoolInit
import Proof.Rows.RowsInitVecDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.I2c.Cache
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.P1Closure NearCubicWires.PacketFamilyParent
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.I2c.VecProg NearCubicWires.BlockPlatform
noncomputable section

/-! ## 1. Length facts about the occurrence stream -/

theorem bf_append {q : ℕ} (g h : List (SupportedNormalizedGate q)) :
    Rounds.bf (g ++ h) = Rounds.bf g ++ Rounds.bf h := by simp [Rounds.bf]

theorem bf_le_segment {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) :
    (Rounds.bf gs).length ≤ (frame (segment gs t)).length := by
  unfold Rounds.bf
  rw [Circuit.segment_split, Circuit.frames_bottoms, frame_length]
  simp only [List.length_append]
  omega

theorem bf_le_flat {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q))
    (topF : C → List Bool) :
    (Rounds.bf (cs.flatMap occF)).length ≤ (cs.flatMap (fun c => frame (segment (occF c) (topF c)))).length := by
  induction cs with
  | nil => simp [Rounds.bf]
  | cons c cs ih =>
    simp only [List.flatMap_cons, bf_append, List.length_append]
    have := bf_le_segment (occF c) (topF c)
    omega

theorem stream_eq_bf {q : ℕ} (occ : List (SupportedNormalizedGate q)) : PoolEntryLoop.stream occ = Rounds.bf occ := rfl

theorem stream_le_nw (a : DecompositionAlgorithm) (r : Request) :
    (PoolEntryLoop.stream (r.family a).occurrences).length ≤ r.nativeWord.length := by
  cases r with
  | terminal => simp [PoolEntryLoop.stream, Request.family]
  | sym r four L target =>
    have h := bf_le_flat r.circuits symmetricCircuitOccurrences (fun c => List.ofFn c.top)
    have hw : Request.nativeWord (.sym r four L target) = natWord 0 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (symmetricCircuitOccurrences c) (List.ofFn c.top))) := by
      simp only [Request.nativeWord, Circuit.symWord_segment]
    rw [hw, stream_eq_bf]
    simp only [List.length_append]
    change (Rounds.bf (symmetricFourfoldOccurrences r)).length ≤ _
    unfold symmetricFourfoldOccurrences
    omega
  | thr r four L target =>
    have h := bf_le_flat r.circuits thresholdCircuitOccurrences
      (fun c => thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate c)))
    have hw : Request.nativeWord (.thr r four L target) = natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (thresholdCircuitOccurrences c)
            (thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate c))))) := by
      simp only [Request.nativeWord, Circuit.thrWord_segment]
    rw [hw, stream_eq_bf]
    simp only [List.length_append]
    change (Rounds.bf (thresholdFourfoldOccurrences r)).length ≤ _
    unfold thresholdFourfoldOccurrences
    omega

theorem stream_le_input (a : DecompositionAlgorithm) (r : Request) :
    (PoolEntryLoop.stream (r.family a).occurrences).length ≤ (r.input a).length :=
  (stream_le_nw a r).trans (Nat.le_of_succ_le (StreamStage.nw_le_input a r))

theorem occ_le_stream {q : ℕ} (occ : List (SupportedNormalizedGate q)) :
    occ.length ≤ (PoolEntryLoop.stream occ).length ∧
      ∀ g ∈ occ, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ (PoolEntryLoop.stream occ).length := by
  induction occ with
  | nil => simp
  | cons g occ ih =>
    have e : PoolEntryLoop.stream (g :: occ) = frame (CloseoutRowsCircuitBottom.nativeWord g) ++ PoolEntryLoop.stream occ :=
      rfl
    rw [e]
    simp only [List.length_append, frame_length, List.length_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro h (rfl | hh)
    · omega
    · have := ih.2 h hh
      omega

/-! ## 2. The seven words -/

/-- `1^P`, `P = PoolCapacity.value B q`. -/
def capStage (a : DecompositionAlgorithm) :
    UnaryStage a (fun r => UnaryCalc.value 3 16777216 ((r.input a).length + r.q)) :=
  ((inputLenStage a).pairP (qStage a) addMap2 6 1 add_cost).thenMapP (RowsInit.LoopWords.polyMap 3 16777216)
    (UnaryCalc.polyCoefficient 3 16777216) (3+1) (RowsInit.LoopWords.poly_cost 3 16777216)

/-- The seven words, as functions of the request. -/
def cacheW (a : DecompositionAlgorithm) : Fin 7 → Request → List Bool :=
  ![fun r => CompareMachine.word r.q, fun r => List.replicate (r.input a).length true,
    fun r => CompareMachine.word (pop a r), fun r => CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a)),
    fun r => PoolEntryLoop.stream (r.family a).occurrences, fun r => UnaryTemplate.tape r.q,
    fun r => List.replicate (UnaryCalc.value 3 16777216 ((r.input a).length + r.q)) true]

/-- Their stages. -/
def cacheS (a : DecompositionAlgorithm) : (j : Fin 7) → WordStage a (cacheW a j)
  | ⟨0, _⟩ => (qStage a).thenWordP cmpWordMap 6 1 cmp_cost
  | ⟨1, _⟩ => (inputLenStage a).toWord
  | ⟨2, _⟩ => (popStage a).thenWordP cmpWordMap 6 1 cmp_cost
  | ⟨3, _⟩ => StreamStage.maskStage a
  | ⟨4, _⟩ => StreamStage.streamStage a
  | ⟨5, _⟩ => (qStage a).tplP
  | ⟨6, _⟩ => (capStage a).toWord

/-- **The seven words, one fixed machine** (RX's `vecOfFn`). -/
def cacheVec (a : DecompositionAlgorithm) := RowsInit.VecDock.vecOfFn a 7 (cacheW a) (cacheS a)

/-! ## 3. The program: the start bank, one head step, the writer and Cold -/

/-- The start-bank producer's 229 tapes: its five inputs are the words (tapes 1–5), the rest private (`8 + k`). -/
def ppSlot (a : DecompositionAlgorithm) (k : Fin 229) : Fin (1 + 7 + (229 + Cold.tapes a)) :=
  ⟨if k.val = 0 then 1 else if k.val = 1 then 2 else if k.val = 62 then 3 else if k.val = 63 then 4
    else if k.val = 64 then 5 else 8 + k.val, by have := k.isLt; split_ifs <;> omega⟩

theorem pp_val (a : DecompositionAlgorithm) (k : Fin 229) : (ppSlot a k).val = if k.val = 0 then 1 else if k.val = 1 then 2
    else if k.val = 62 then 3 else if k.val = 63 then 4 else if k.val = 64 then 5 else 8 + k.val := rfl

theorem pp_inj (a : DecompositionAlgorithm) : Function.Injective (ppSlot a) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [pp_val, pp_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The writer-and-Cold bank: its 132 writer tapes ARE the start bank (`101 + m`), the cache port is the output (0), the arity
template and `1^P` are the words 6 and 7, the rest private (`237 + c`). -/
def rdSlot (a : DecompositionAlgorithm) (m : Fin (132 + Cold.tapes a)) : Fin (1 + 7 + (229 + Cold.tapes a)) :=
  ⟨if m.val < 132 then 101 + m.val else if m.val = 132 + (SB a + 4) then 0 else if m.val = 132 + (SB a + 10) then 6
    else if m.val = 132 + (SB a + 14) then 7 else 237 + (m.val - 132), by have := m.isLt; split_ifs <;> omega⟩

theorem rd_val (a : DecompositionAlgorithm) (m : Fin (132 + Cold.tapes a)) : (rdSlot a m).val =
    if m.val < 132 then 101 + m.val else if m.val = 132 + (SB a + 4) then 0 else if m.val = 132 + (SB a + 10) then 6
    else if m.val = 132 + (SB a + 14) then 7 else 237 + (m.val - 132) := rfl

theorem rd_inj (a : DecompositionAlgorithm) : Function.Injective (rdSlot a) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [rd_val, rd_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def mvDir (a : DecompositionAlgorithm) (i : Fin (1 + 7 + (229 + Cold.tapes a))) : HeadMove := if i.val = 6 then HeadMove.right else HeadMove.stay

/-- **The cache program** (one fixed machine per `a`). -/
def cacheM (a : DecompositionAlgorithm) :=
  Composition.machine (Composition.machine (RecoveryFocus.machine (ppSlot a) PoolProduced.machine)
    (DecompositionCountPosition.move (mvDir a))) (RecoveryFocus.machine (rdSlot a) (PoolReady.readyMachine a))

theorem pp_input {q : ℕ} (live : Finset (Fin q)) (B N : ℕ) (S : List Bool) (k : Fin 229) :
    PoolProduced.input live B N S k = if k.val = 0 then CompareMachine.word q else if k.val = 1 then List.replicate B true
      else if k.val = 62 then CompareMachine.word N else if k.val = 63 then CloseoutRowsGateSupport.gateMembers live
      else if k.val = 64 then S else [] := by
  fin_cases k <;> rfl

theorem slots_worker (i : Fin 132) : (PoolProduced.slots (PoolInitialize.worker i)).val = 93 + i.val := by
  have hw : (PoolInitialize.worker i).val = 9 + i.val := by
    simp only [PoolInitialize.worker, PoolAllocate.worker, Fin.val_castAdd, Fin.val_natAdd]
  simp only [PoolProduced.slots]
  split_ifs with h1 h2
  · omega
  · have := congrArg Fin.val h2
    simp only [hw] at this
    have := i.isLt
    omega
  · simp [hw]
    omega

theorem start_tapes {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (B : ℕ) :
    (PoolCold.start live occ B (B+q+1) []).tapes =
      PoolBank.startBank live B occ.length (PoolEntryLoop.stream occ) := rfl

theorem start_heads {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (B : ℕ) :
    (PoolCold.start live occ B (B+q+1) []).heads = PoolInitialize.head occ.length := by
  funext i; fin_cases i <;> rfl

def cacheCost (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  PoolProduced.budget (r.input a).length r.q (r.family a).occurrences.length+1+1+1+
    PoolReady.budget a (r.family a).occurrences (r.input a).length ((r.input a).length+r.q+1)
      (PoolCapacity.value (r.input a).length r.q)

theorem pIn_word (a : DecompositionAlgorithm) (r : Request) (j : ℕ) (hj : j < 7) :
    pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r ⟨j+1, by omega⟩ = cacheW a ⟨j, hj⟩ r := by
  simp only [pIn]
  rw [if_pos (by omega)]
  simp [RowsInit.VecDock.vecOuts, hj]

theorem pIn_blank (a : DecompositionAlgorithm) (r : Request) (i : Fin (1 + 7 + (229 + Cold.tapes a)))
    (h : i.val = 0 ∨ 8 ≤ i.val) : pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r i = [] := by
  simp only [pIn]
  rw [if_neg (by omega)]

theorem port_cch_val (a : DecompositionAlgorithm) : (Cold.port a (cch a)).val = SB a + 4 := rfl

theorem cache_val (a : DecompositionAlgorithm) : (PoolReady.cachePort a).val = 132 + (SB a + 4) := by
  have hne : Cold.port a (cch a) ≠ PoolCold.sourcePort a := by
    intro h
    have hv := congrArg Fin.val h
    rw [port_cch_val, PoolCold.sourcePort_val] at hv
    omega
  unfold PoolReady.cachePort PoolCold.slots
  rw [if_neg hne, Fin.val_natAdd, port_cch_val]

theorem mv_on (a : DecompositionAlgorithm) (i : Fin (1 + 7 + (229 + Cold.tapes a))) (h : i.val = 6) (x : ℕ) :
    (mvDir a i).apply x = x + 1 := by simp [mvDir, h, HeadMove.apply]

theorem mv_off (a : DecompositionAlgorithm) (i : Fin (1 + 7 + (229 + Cold.tapes a))) (h : i.val ≠ 6) (x : ℕ) :
    (mvDir a i).apply x = x := by simp [mvDir, h, HeadMove.apply]

theorem rd_worker (a : DecompositionAlgorithm) (i : Fin 132) :
    rdSlot a (Fin.castAdd (Cold.tapes a) i) = ppSlot a (PoolProduced.slots (PoolInitialize.worker i)) := by
  apply Fin.ext
  rw [rd_val, pp_val, slots_worker]
  have := i.isLt
  simp only [Fin.val_castAdd]
  split_ifs <;> omega

theorem rd_cold (a : DecompositionAlgorithm) (c : Fin (Cold.tapes a)) : (rdSlot a (Fin.natAdd 132 c)).val =
    if c.val = SB a + 4 then 0 else if c.val = SB a + 10 then 6 else if c.val = SB a + 14 then 7 else 237 + c.val := by
  rw [rd_val]
  simp only [Fin.val_natAdd]
  split_ifs <;> omega

/-- **The cache program's run**: from the seven words, the child cache on tape 0. -/
theorem cache_run (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H : Fin (1 + 7 + (229 + Cold.tapes a)) → ℕ) (A : Fin (1 + 7 + (229 + Cold.tapes a)) → List Bool),
      Step (cacheM a) (cacheCost a r) (fun _ => 0)
        (pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r) H A ∧
      A ⟨0, by omega⟩ = exactListWord (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a
        (Packets.live (r.family a)) (r.family a).occurrences) := by
  have hSB : (PoolEntryLoop.stream (r.family a).occurrences).length ≤ (r.input a).length := stream_le_input a r
  obtain ⟨hNS, hgS⟩ := occ_le_stream (r.family a).occurrences
  have hN : (r.family a).occurrences.length ≤ (r.input a).length := hNS.trans hSB
  have hb : ∀ g ∈ (r.family a).occurrences, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ (r.input a).length :=
    fun g hg => (hgS g hg).trans hSB
  have hsmall := PoolCapacity.small_bounds (r.input a).length r.q
  have hBP : (r.input a).length ≤ PoolCapacity.value (r.input a).length r.q := by
    have h1 : ((r.input a).length + r.q + 1)^1 ≤ ((r.input a).length + r.q + 1)^3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_one] at h1
    change (r.input a).length ≤ 16777216*((r.input a).length+r.q+1)^3
    omega
  -- stage 1: the start bank
  obtain ⟨H1, A1, s1, hh1, ha1⟩ := PoolProduced.run (Packets.live (r.family a)) (r.input a).length
    (r.family a).occurrences.length (PoolEntryLoop.stream (r.family a).occurrences) hN (hSB.trans hBP)
  have d1 := s1.dock (ppSlot a) (pp_inj a) (fun _ => 0)
      (pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r) (fun _ => rfl) (by
    intro k
    rw [pp_input]
    by_cases k0 : k.val = 0
    · have e : ppSlot a k = ⟨0+1, by omega⟩ := Fin.ext (by rw [pp_val]; simp [k0])
      rw [e, pIn_word a r 0 (by omega)]
      simp [k0, cacheW]
    by_cases k1 : k.val = 1
    · have e : ppSlot a k = ⟨1+1, by omega⟩ := Fin.ext (by rw [pp_val]; simp [k1])
      rw [e, pIn_word a r 1 (by omega)]
      simp [k1, cacheW]
    by_cases k2 : k.val = 62
    · have e : ppSlot a k = ⟨2+1, by omega⟩ := Fin.ext (by rw [pp_val]; simp [k2])
      rw [e, pIn_word a r 2 (by omega)]
      simp [k2, cacheW]
      rfl
    by_cases k3 : k.val = 63
    · have e : ppSlot a k = ⟨3+1, by omega⟩ := Fin.ext (by rw [pp_val]; simp [k3])
      rw [e, pIn_word a r 3 (by omega)]
      simp [k3, cacheW]
    by_cases k4 : k.val = 64
    · have e : ppSlot a k = ⟨4+1, by omega⟩ := Fin.ext (by rw [pp_val]; simp [k4])
      rw [e, pIn_word a r 4 (by omega)]
      simp [k4, cacheW]
    · rw [pIn_blank a r _ (Or.inr (by rw [pp_val]; simp [k0, k1, k2, k3, k4]))]
      simp [k0, k1, k2, k3, k4])
  -- stage 2: one step of the arity template's head
  have s2 := RowsConstruction.I2c.Stream.move_step (mvDir a) (dockH (ppSlot a) (fun _ => 0) H1)
    (install (ppSlot a) (pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r) A1)
  -- stage 3: the writer and Cold, padded
  have hi : (segment (NearCubicWires.RepairSource.CloseoutRowsUniversal.pool (Packets.live (r.family a))
      (r.family a).occurrences) []).length ≤ 1000*(PoolCapacity.value (r.input a).length r.q+2)^2 := by
    have h := PoolCapacity.segment_bound (Packets.live (r.family a)) (r.family a).occurrences (r.input a).length hN hb
    have h2 : PoolCapacity.value (r.input a).length r.q ≤ 1000*(PoolCapacity.value (r.input a).length r.q+2)^2 := by
      nlinarith
    exact h.trans h2
  obtain ⟨H3, A3, s3, _, hc, _, _⟩ := PoolReady.ready_run a (Packets.live (r.family a)) (r.family a).occurrences
    (r.input a).length ((r.input a).length+r.q+1) (PoolCapacity.value (r.input a).length r.q) [] (by omega) (by omega) hb
    (fun g hg => PoolAdmissions.magnitude g (hb g hg)) (by omega) hi
  have s3p := s3.pad (fun m => if m.val < 132 then PoolCapacity.value (r.input a).length r.q else 0)
  have offpp : ∀ i : Fin (1 + 7 + (229 + Cold.tapes a)), (i.val = 0 ∨ i.val = 6 ∨ i.val = 7 ∨ 237 ≤ i.val) →
      ∀ k, ppSlot a k ≠ i := by
    intro i hi k hk
    have hv := congrArg Fin.val hk
    rw [pp_val] at hv
    have := k.isLt
    split_ifs at hv <;> omega
  have d3 := s3p.dock (rdSlot a) (rd_inj a) (fun i => (mvDir a i).apply (dockH (ppSlot a) (fun _ => 0) H1 i))
    (install (ppSlot a) (pIn 7 (229 + Cold.tapes a) (RowsInit.VecDock.vecOuts (cacheW a)) r) A1)
    (by
      intro m
      refine Fin.addCases (fun i => ?_) (fun c => ?_) m
      · rw [Fin.addCases_left, start_heads, rd_worker]
        have h6 : (ppSlot a (PoolProduced.slots (PoolInitialize.worker i))).val ≠ 6 := by
          rw [pp_val, slots_worker]; split_ifs <;> omega
        change (mvDir a _).apply _ = _
        rw [mv_off a _ h6, dockH_slot _ (pp_inj a), hh1]
      · rw [Fin.addCases_right]
        change (mvDir a _).apply _ = Cold.heads a 0 c
        simp only [Cold.heads]
        have hc := c.isLt
        have hv := rd_cold a c
        by_cases c10 : c.val = SB a + 10
        · have h6 : (rdSlot a (Fin.natAdd 132 c)).val = 6 := by rw [hv]; simp [c10]
          rw [mv_on a _ h6, dockH_other _ _ _ _ (offpp _ (Or.inr (Or.inl h6)))]
          simp [c10]
        · have h6 : (rdSlot a (Fin.natAdd 132 c)).val ≠ 6 := by rw [hv]; split_ifs <;> omega
          have hoff : (rdSlot a (Fin.natAdd 132 c)).val = 0 ∨ (rdSlot a (Fin.natAdd 132 c)).val = 6 ∨
              (rdSlot a (Fin.natAdd 132 c)).val = 7 ∨ 237 ≤ (rdSlot a (Fin.natAdd 132 c)).val := by
            rw [hv]; split_ifs <;> omega
          rw [mv_off a _ h6, dockH_other _ _ _ _ (offpp _ hoff)]
          split_ifs <;> rfl)
    (by
      intro m
      refine Fin.addCases (fun i => ?_) (fun c => ?_) m
      · rw [Fin.addCases_left, start_tapes, rd_worker, install_slot _ (pp_inj a), ha1]
        simp
      · rw [Fin.addCases_right]
        change _ = ZeroPadding.pad (if 132 + c.val < 132 then _ else 0) (Cold.data a _ r.q [] c)
        rw [if_neg (by omega), ZeroPadding.pad_zero]
        simp only [Cold.data]
        have hc := c.isLt
        have hv := rd_cold a c
        have hoff : (rdSlot a (Fin.natAdd 132 c)).val = 0 ∨ (rdSlot a (Fin.natAdd 132 c)).val = 6 ∨
            (rdSlot a (Fin.natAdd 132 c)).val = 7 ∨ 237 ≤ (rdSlot a (Fin.natAdd 132 c)).val := by
          rw [hv]; split_ifs <;> omega
        rw [install_other _ _ _ _ (offpp _ hoff)]
        by_cases c10 : c.val = SB a + 10
        · have e : rdSlot a (Fin.natAdd 132 c) = ⟨5+1, by omega⟩ := Fin.ext (by rw [hv]; simp [c10])
          rw [e, pIn_word a r 5 (by omega)]
          simp [c10, cacheW]
        by_cases c14 : c.val = SB a + 14
        · have e : rdSlot a (Fin.natAdd 132 c) = ⟨6+1, by omega⟩ := Fin.ext (by rw [hv]; simp [c14])
          rw [e, pIn_word a r 6 (by omega)]
          simp [c14, cacheW]
          rfl
        · rw [pIn_blank a r _ (by rw [hv]; split_ifs <;> omega)]
          split_ifs <;> rfl)
  refine ⟨_, _, (d1.seq s2).seq d3, ?_⟩
  have e : (⟨0, by omega⟩ : Fin (1 + 7 + (229 + Cold.tapes a))) = rdSlot a (PoolReady.cachePort a) :=
    Fin.ext (by rw [rd_val, cache_val]; simp)
  rw [e, install_slot _ (rd_inj a)]
  have hcap : (fun m : Fin (132 + Cold.tapes a) => if m.val < 132 then PoolCapacity.value (r.input a).length r.q else 0)
      (PoolReady.cachePort a) = 0 := by
    simp only [cache_val]; rw [if_neg (by omega)]
  simp only [hcap, ZeroPadding.pad_zero]
  exact hc

/-! ## 4. The program's cost: a fixed polynomial of `B+q+1` (for the fixed `a`) -/

def Dc (a : DecompositionAlgorithm) : ℕ := 4 + 3*ColdBudget.runtimeDegree a
def Kc (a : DecompositionAlgorithm) : ℕ :=
  UnaryCalc.polyCoefficient 3 16777216 + UnaryCalc.polyCoefficient 2 262144 + 2^26 +
    ColdBudget.runtimeCoefficient a * 16777218^ColdBudget.runtimeDegree a

theorem cacheCost_le (a : DecompositionAlgorithm) (r : Request) :
    cacheCost a r ≤ Kc a * ((r.input a).length + r.q + 1)^(Dc a) := by
  have hSB : (PoolEntryLoop.stream (r.family a).occurrences).length ≤ (r.input a).length := stream_le_input a r
  have hN : (r.family a).occurrences.length ≤ (r.input a).length := (occ_le_stream (r.family a).occurrences).1.trans hSB
  unfold cacheCost PoolProduced.budget PoolMasters.budget PoolPreparation.budget PoolDrivers.budget
    PoolScalars.budget PoolHeader.budget PoolInitialize.budget PoolReady.budget
  generalize (r.family a).occurrences = occ at hN ⊢
  generalize (r.input a).length = B at hN ⊢
  have p3 := UnaryCalc.poly_cost_polyBounded 3 16777216 (B+r.q)
  have p2 := UnaryCalc.poly_cost_polyBounded 2 262144 (B+r.q)
  unfold ValidatorPolynomialDomination.PolyBounded at p3 p2
  have hval : PoolCapacity.value B r.q = 16777216*(B+r.q+1)^3 := rfl
  rw [hval]
  have hdp := NearCubicWires.RepairSource.ProjectionNormalization.DimensionPower.cost_bound 1 8 (B+r.q+1) 1 le_rfl
  rw [CacheBudget.loop_eq]
  generalize hMd : B + r.q + 1 = M at p3 p2 hdp ⊢
  have hM : 1 ≤ M := by omega
  have pw : ∀ k, k ≤ Dc a → M^k ≤ M^(Dc a) := fun k hk => Nat.pow_le_pow_right hM hk
  have x1 := pw 1 (by unfold Dc; omega)
  have x2 := pw 2 (by unfold Dc; omega)
  have x3 := pw 3 (by unfold Dc; omega)
  have x4 := pw 4 (by unfold Dc; omega)
  have x3r := pw (3*ColdBudget.runtimeDegree a) (by unfold Dc; omega)
  rw [pow_one] at x1
  have e4 : M^(3+1) = M^4 := rfl
  have e3 : M^(2+1) = M^3 := rfl
  rw [e4] at p3
  rw [e3] at p2
  have p3' := Nat.mul_le_mul_left (UnaryCalc.polyCoefficient 3 16777216) x4
  have p2' := Nat.mul_le_mul_left (UnaryCalc.polyCoefficient 2 262144) x3
  have hdp2 : (M+1)^(1+1) ≤ 4*M^2 := by
    have : (M+1)^(1+1) ≤ (2*M)^2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hbit : natBitLength (2*occ.length) ≤ 2*occ.length+1 :=
    Nat.add_le_add_right (Nat.log_le_self 2 (2*occ.length)) 1
  have hhdr : NearCubicWires.RepairOrdinary.EquationNaturalHeader.budget (2*occ.length) ≤ 300*M^2 := by
    unfold NearCubicWires.RepairOrdinary.EquationNaturalHeader.budget
    have h1 : occ.length ≤ M := by omega
    have h2 : (2*occ.length)^2 ≤ 4*M^2 := by
      have := Nat.pow_le_pow_left (show 2*occ.length ≤ 2*M by omega) 2
      nlinarith
    have h3 : M ≤ M^2 := by nlinarith
    omega
  have hloop : occ.length*(409600*(B+r.q+M+1)^2+4*B+25)+3 ≤ 1638432*M^3 := by
    have e : B+r.q+M+1 = 2*M := by omega
    rw [e]
    have h1 : occ.length ≤ M := by omega
    have h2 : occ.length*(409600*(2*M)^2+4*B+25) ≤ M*(409600*(2*M)^2+4*M+25) :=
      Nat.mul_le_mul h1 (by omega)
    have h3 : M*(409600*(2*M)^2+4*M+25) = 1638400*M^3+4*M^2+25*M := by ring
    have h4 : M^2 ≤ M^3 := Nat.pow_le_pow_right hM (by omega)
    have h5 : M ≤ M^3 := by
      have := Nat.pow_le_pow_right hM (show 1 ≤ 3 by omega); rwa [pow_one] at this
    omega
  have hcold : ColdBudget.runtimeCoefficient a * (16777216*M^3+2)^ColdBudget.runtimeDegree a ≤
      ColdBudget.runtimeCoefficient a * 16777218^ColdBudget.runtimeDegree a * M^(Dc a) := by
    have h1 : 16777216*M^3+2 ≤ 16777218*M^3 := by
      have : 1 ≤ M^3 := Nat.one_le_pow _ _ hM
      omega
    have h2 : (16777216*M^3+2)^ColdBudget.runtimeDegree a ≤ (16777218*M^3)^ColdBudget.runtimeDegree a :=
      Nat.pow_le_pow_left h1 _
    rw [mul_pow, ← pow_mul] at h2
    have h3 := Nat.mul_le_mul_left (16777218^ColdBudget.runtimeDegree a) x3r
    calc ColdBudget.runtimeCoefficient a * (16777216*M^3+2)^ColdBudget.runtimeDegree a
        ≤ ColdBudget.runtimeCoefficient a * (16777218^ColdBudget.runtimeDegree a * M^(3*ColdBudget.runtimeDegree a)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ ColdBudget.runtimeCoefficient a * (16777218^ColdBudget.runtimeDegree a * M^(Dc a)) :=
          Nat.mul_le_mul_left _ h3
      _ = ColdBudget.runtimeCoefficient a * 16777218^ColdBudget.runtimeDegree a * M^(Dc a) := by ring
  have hKX : Kc a * M^(Dc a) = UnaryCalc.polyCoefficient 3 16777216 * M^(Dc a) +
      UnaryCalc.polyCoefficient 2 262144 * M^(Dc a) + 2^26 * M^(Dc a) +
      ColdBudget.runtimeCoefficient a * 16777218^ColdBudget.runtimeDegree a * M^(Dc a) := by unfold Kc; ring
  rw [hKX]
  omega

theorem cacheCost_small (a : DecompositionAlgorithm) (r : Request) :
    cacheCost a r ≤ (Kc a * 2^(Dc a)) * (r.smallSize a)^(Dc a) := by
  have h := cacheCost_le a r
  have hq := PolyBound.q_input_le_smallSize a r
  have hs := one_le_small a r
  have h1 : (r.input a).length + r.q + 1 ≤ 2 * r.smallSize a := by omega
  have h2 : ((r.input a).length + r.q + 1)^(Dc a) ≤ (2 * r.smallSize a)^(Dc a) := Nat.pow_le_pow_left h1 _
  rw [mul_pow] at h2
  calc cacheCost a r ≤ Kc a * ((r.input a).length + r.q + 1)^(Dc a) := h
    _ ≤ Kc a * (2^(Dc a) * (r.smallSize a)^(Dc a)) := Nat.mul_le_mul_left _ h2
    _ = (Kc a * 2^(Dc a)) * (r.smallSize a)^(Dc a) := by ring

/-- **The cache program** as a `Prog` on the seven words. -/
def cacheProg (a : DecompositionAlgorithm) : Prog a 7 (RowsInit.VecDock.vecOuts (cacheW a))
    (fun r => exactListWord (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a
      (Packets.live (r.family a)) (r.family a).occurrences)) where
  extra := 229 + Cold.tapes a
  states := _
  machine := cacheM a
  cost := cacheCost a
  coefficient := Kc a * 2^(Dc a)
  degree := Dc a
  cost_le := cacheCost_small a
  run := cache_run a

/-- **The child cache as a request stage** (one fixed machine per `a`). -/
def cacheStage (a : DecompositionAlgorithm) : WordStage a (fun r => exactListWord
    (NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.childList a (Packets.live (r.family a))
      (r.family a).occurrences)) :=
  VecStage.thenProg (cacheVec a) (cacheProg a)

end
end RowsConstruction.I2c.Cache
