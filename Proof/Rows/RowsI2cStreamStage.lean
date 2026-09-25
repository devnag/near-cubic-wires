import Proof.Rows.RowsI2cStream
import Proof.Packets.PacketsMetaWord
import Proof.SourceAssembly.PoolDonorCompatible

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.I2c.StreamStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.P1Closure NearCubicWires.CompilerSemantics
open NearCubicWires.PacketFamilyParent
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.I2c.Rounds RowsConstruction.I2c.Stream
noncomputable section

/-! ## 1. At most four payloads, padded to exactly four -/

theorem pad4 {q : ℕ} (LP : List (List (SupportedNormalizedGate q) × List Bool)) (hL : LP.length ≤ 4) :
    ∃ (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool) (rest : List Bool),
      (LP.map fr).flatten ++ P4 = ([p0, p1, p2, p3].map fr).flatten ++ rest ∧
      [p0, p1, p2, p3].flatMap Prod.fst = LP.flatMap Prod.fst := by
  have d := fr_nil q
  match LP, hL with
  | [], _ => exact ⟨([], []), ([], []), ([], []), ([], []), [], by simp [P4, d], by simp⟩
  | [x0], _ => exact ⟨x0, ([], []), ([], []), ([], []), frame W0, by simp [P4, d], by simp⟩
  | [x0, x1], _ => exact ⟨x0, x1, ([], []), ([], []), frame W0 ++ frame W0, by simp [P4, d], by simp⟩
  | [x0, x1, x2], _ => exact ⟨x0, x1, x2, ([], []), frame W0 ++ (frame W0 ++ frame W0), by simp [P4, d], by simp⟩
  | [x0, x1, x2, x3], _ => exact ⟨x0, x1, x2, x3, P4, by simp, by simp⟩
  | _ :: _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-! ## 2. The cost bound of the main branch -/

theorem fr_length {q : ℕ} (p : List (SupportedNormalizedGate q) × List Bool) :
    (fr p).length = 2*(segment p.1 p.2).length+1 := by simp [fr, frame_length]

theorem main_bound {q : ℕ} (n1 n2 n3 n4 n5 : ℕ) (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool)
    (rest nw : List Bool)
    (hnw : nw ++ P4 = natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++
      (([p0, p1, p2, p3].map fr).flatten ++ rest)))))) :
    preCost nw+1+1+1+(mainCost n1 n2 n3 n4 n5 [p0, p1, p2, p3]+2) ≤ xBound nw.length := by
  have hl := congrArg List.length hnw
  simp only [List.length_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    fr_length, P4_length, DecompositionSource.natWord_length] at hl
  have r0 := roundCost_le p0.1 p0.2
  have r1 := roundCost_le p1.1 p1.2
  have r2 := roundCost_le p2.1 p2.2
  have r3 := roundCost_le p3.1 p3.2
  unfold preCost mainCost sk5Cost xBound
  simp only [iterCost, P4_length]
  omega

/-! ## 3. The extractor on every request -/

theorem flat_map_fr {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    ((cs.map (fun c => (occF c, topF c))).map fr).flatten = cs.flatMap (fun c => frame (segment (occF c) (topF c))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih, fr]

theorem flat_fst {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    (cs.map (fun c => (occF c, topF c))).flatMap Prod.fst = cs.flatMap occF := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.flatMap_cons, ih]

/-- The THR/SYM shape: tag `k ∈ {0,1}`, four header naturals, the circuit payloads. -/
theorem x_mode {q : ℕ} {C : Type} (k qv L tg : ℕ) (hk : natBitLength k = 1) (cs : List C) (h4 : cs.length ≤ 4)
    (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0)
        (xIn (frame (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
          cs.flatMap (fun c => frame (segment (occF c) (topF c)))))) H A ∧
      A 1 = bf (cs.flatMap occF) ∧
      n ≤ xBound (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
          cs.flatMap (fun c => frame (segment (occF c) (topF c)))).length := by
  obtain ⟨p0, p1, p2, p3, rest, hp, hf⟩ :=
    pad4 (cs.map (fun c => (occF c, topF c))) (by simp [h4])
  rw [flat_map_fr] at hp
  rw [flat_fst] at hf
  have hnw : (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
      cs.flatMap (fun c => frame (segment (occF c) (topF c)))) ++ P4 =
      natWord k ++ (natWord qv ++ (natWord L ++ (natWord tg ++ (natWord cs.length ++
        (([p0, p1, p2, p3].map fr).flatten ++ rest))))) := by
    simp only [List.append_assoc, hp]
  have hb : readTapeBit ((natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
      cs.flatMap (fun c => frame (segment (occF c) (topF c)))) ++ P4) 1 = false := by
    rw [hnw]
    exact tag_bit k hk _
  obtain ⟨n, H, A, s, a1, hn⟩ := x_main k qv L tg cs.length p0 p1 p2 p3 rest _ hnw hb
  exact ⟨n, H, A, s, by rw [a1, hf], hn.trans (main_bound k qv L tg cs.length p0 p1 p2 p3 rest _ hnw)⟩

/-- **The extractor on every request.** -/
theorem x_request (a : DecompositionAlgorithm) (r : Request) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0) (xIn (frame r.nativeWord)) H A ∧
      A 1 = PoolEntryLoop.stream (r.family a).occurrences ∧ n ≤ xBound r.nativeWord.length := by
  cases r with
  | terminal =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_stop (natWord 2) (tag_bit_two P4)
    exact ⟨n, H, A, s, a1, hn⟩
  | sym r four L target =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_mode 0 r.q L target bitLength_zero r.circuits four
      symmetricCircuitOccurrences (fun c => List.ofFn c.top)
    have hw : Request.nativeWord (.sym r four L target) = natWord 0 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (symmetricCircuitOccurrences c) (List.ofFn c.top))) := by
      simp only [Request.nativeWord, Circuit.symWord_segment]
    rw [hw]
    exact ⟨n, H, A, s, a1, hn⟩
  | thr r four L target =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_mode 1 r.q L target bitLength_one r.circuits four
      thresholdCircuitOccurrences (fun c => thresholdWord (nonStrictAsStrict (retainedTopGate c)))
    have hw : Request.nativeWord (.thr r four L target) = natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (thresholdCircuitOccurrences c)
            (thresholdWord (nonStrictAsStrict (retainedTopGate c))))) := by
      simp only [Request.nativeWord, Circuit.thrWord_segment]
    rw [hw]
    exact ⟨n, H, A, s, a1, hn⟩

/-! ## 4. The two word stages -/

theorem nw_le_input (a : DecompositionAlgorithm) (r : Request) : r.nativeWord.length+1 ≤ (r.input a).length := by
  have h := field_le_input a r 0
  change (frame r.nativeWord).length ≤ _ at h
  rw [frame_length] at h
  omega

theorem stream_run (a : DecompositionAlgorithm) (r : Request) :
    ∃ (H' : Fin (2 + (13 + 52 + 1)) → ℕ) (A' : Fin (2 + (13 + 52 + 1)) → List Bool),
      Step (fieldMachineE (e := 52) xM 0) (6*(r.input a).length+17 + 1 + (2*xBound r.nativeWord.length+2)) (fun _ => 0)
        (inBank (2 + (13 + 52 + 1)) (Request.input a r)) H' A' ∧
      A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
      A' ⟨1, by omega⟩ = PoolEntryLoop.stream (r.family a).occurrences ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨n, H, A, s, a1, hn⟩ := x_request a r
  have s' : Step xM (xBound r.nativeWord.length) (fun _ => 0) (scanIn 52 (frame (fields a r 0))) H A :=
    s.enlarge hn
  exact field_runW (e := 52) xM 0 a r _ (xBound r.nativeWord.length) H A s' a1

/-- **The occurrence stream as a request stage.** -/
def streamStage (a : DecompositionAlgorithm) : WordStage a (fun r => PoolEntryLoop.stream (r.family a).occurrences) where
  extra := 13 + 52 + 1
  states := _
  machine := fieldMachineE (e := 52) xM 0
  cost := fun r => 6*(r.input a).length+17+1+(2*xBound r.nativeWord.length+2)
  coefficient := 400*31
  degree := 1
  cost_le := by
    intro r
    have h1 := nw_le_input a r
    have h2 := input_le_small a r
    unfold xBound
    rw [pow_one]
    omega
  run := stream_run a

/-- **The live mask as a request stage** (input field 2, unframed). -/
def maskStage (a : DecompositionAlgorithm) :
    WordStage a (fun r => CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a))) where
  extra := 13 + 0 + 1
  states := _
  machine := fieldMachineE (e := 0) GeneratedAmplifier.Copy.machine 2
  cost := fun r => 6*(r.input a).length+17+1+(2*(2*(fields a r 2).length+1)+2)
  coefficient := 30
  degree := 1
  cost_le := by
    intro r
    have h1 := field_le_input a r 2
    have h2 := input_le_small a r
    rw [frame_length] at h1
    rw [pow_one]
    omega
  run := by
    intro r
    have u := Circuit.unframe_step [] (fields a r 2) [] []
    simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at u
    have e1 : (![0, 0] : Fin 2 → ℕ) = fun _ => 0 := by funext i; fin_cases i <;> rfl
    have e2 : (![frame (fields a r 2), []] : Fin 2 → List Bool) = scanIn 0 (frame (fields a r 2)) := by
      funext i; fin_cases i <;> rfl
    rw [e1, e2] at u
    exact field_runW (e := 0) GeneratedAmplifier.Copy.machine 2 a r _ _ _ _ u rfl

end
end RowsConstruction.I2c.StreamStage
