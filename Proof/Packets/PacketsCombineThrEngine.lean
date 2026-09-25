import Proof.Packets.PacketsCombineSweep
import Proof.Packets.PhysicalIndexReload

/-! # P2 (iii) kit core: the THR radix-row engine (ordered parity over all digit tuples)

Consumer: `ThrCombineStageK.run` (`Proof/Packets/PacketsRowPolySplitKit.lean`): tape 14 must carry the kit
register of `Normalized.structuralGF2ModularRadixRow p residue 2 coord`
(`PacketsRowPolyPlan.thr_rowPoly`, `rfl`) = `FinParity (fun code => term code)` =
`foldr Ring.add [] [term 0, …, term (N-1)]` (`NormalizedFolds.finiteParity_foldr`),
`N = (pop+1)^digits`. Paper: A.13.7 (`paper.tex:3113-3142`): the internal tuples are preprocessing
inside the row's `T_prep` charge (`paper.tex:1197-1200`); budget class source-polynomial (the tuple
count `N` is the `tupleWork` summand of `smallSize`).

This module is the MACHINE: codes are processed in DESCENDING order, so a parked register runs
through the suffix parities, exactly the frozen right fold. Each code reads one block of a
selection TABLE (tape 37): `K = digits*m` selection bits (bank position `p` is multiplied in iff
its bit is set) followed by the code's acceptance bit. Per code: move the table cursor onto the
acceptance bit; `acc := [[]]` iff accepted (`PhysicalBitCall` + `OrderedPacketReset.one_run`);
reload the bank index `K` (`PhysicalIndexReload`); the filtered product sweep (`sweep_run`);
then `park := add acc park` through the arena (`OrderedPacketStep.add_run`) and three register
copies; `acc := []`. The table's CONTENT (which tuple, which acceptance) is the semantic layer's
business (`PacketsCombineThrMeaning`), not this module's.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-! ## Semantics of one code's block -/

/-- The accumulator's initial value for the code whose block starts at `base`. -/
def initAcc (table : List Bool) (base K : ℕ) : Poly := if table.getD (base + K) false then [[]] else []

/-- The term a code contributes: the filtered product over its block. -/
def codeTerm (ps : List Poly) (table : List Bool) (K c : ℕ) : Poly :=
  sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) K

/-- The parked register after `j` codes (the last `j` codes' ordered parity). -/
def thrParkAt (ps : List Poly) (table : List Bool) (N K j : ℕ) : Poly :=
  ((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).drop (N - j)).foldr Ring.add []

def thrLeftAt (ps : List Poly) (table : List Bool) (N K : ℕ) (left0 : Poly) (j : ℕ) : Poly :=
  if j = 0 then left0 else codeTerm ps table K (N - j)

theorem thrParkAt_zero (ps : List Poly) (table : List Bool) (N K : ℕ) : thrParkAt ps table N K 0 = [] := by
  unfold thrParkAt
  rw [Nat.sub_zero, List.drop_of_length_le (by simp)]
  rfl

theorem thrParkAt_succ (ps : List Poly) (table : List Bool) (N K j : ℕ) (hj : j < N) :
    thrParkAt ps table N K (j + 1) = Ring.add (codeTerm ps table K (N - (j + 1))) (thrParkAt ps table N K j) := by
  unfold thrParkAt
  have hk : N - (j + 1) < (List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).length := by simp; omega
  rw [List.drop_eq_getElem_cons hk, List.foldr_cons]
  have he : N - (j + 1) + 1 = N - j := by omega
  rw [he]
  congr 1
  simp

theorem thrParkAt_full (ps : List Poly) (table : List Bool) (N K : ℕ) :
    thrParkAt ps table N K N = (List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add [] := by
  unfold thrParkAt
  rw [Nat.sub_self, List.drop_zero]

theorem thrParkAt_bounded (S : Finset ℕ) (e : ℕ) (ps : List Poly) (table : List Bool) (N K j : ℕ)
    (hterm : ∀ c, c < N → NormalizedIntermediate.Bounded S e (codeTerm ps table K c)) :
    NormalizedIntermediate.Bounded S e (thrParkAt ps table N K j) := by
  unfold thrParkAt
  generalize hl : (List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).drop (N - j) = l
  have hall : ∀ P ∈ l, NormalizedIntermediate.Bounded S e P := by
    intro P hP
    rw [← hl] at hP
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hP)
    exact hterm c.val c.isLt
  clear hl
  induction l with
  | nil => exact NormalizedIntermediate.zero S e
  | cons P l ih =>
    rw [List.foldr_cons]
    exact NormalizedIntermediate.add (hall P (by simp)) (ih (fun Q hQ => hall Q (by simp [hQ])))

/-! ## Layout: the combine body layout plus a stored index word -/

def thrA (C R index K : ℕ) (left acc : Poly) (ps : List Poly) (table : List Bool) (P : Poly) (stored : List Bool) :
    Fin 42 → List Bool :=
  Fin.addCases (m := 41) (n := 1) (motive := fun _ => List Bool) (bodyA C R index K left acc ps table P)
    (fun _ => stored)

def thrH (pos : ℕ) : Fin 42 → ℕ :=
  Fin.addCases (m := 41) (n := 1) (motive := fun _ => ℕ) (bodyH pos) (fun _ => 0)

/-- A 38-tape (arena + table) machine lifted into the THR layout. -/
def emb38 {s : ℕ} (p : Machine 38 s) := TapeEmbedding.machine 1 (TapeEmbedding.machine 2 (TapeEmbedding.machine 1 p))
/-- A 41-tape (combine body) machine lifted into the THR layout. -/
def emb41 {s : ℕ} (p : Machine 41 s) := TapeEmbedding.machine 1 p

theorem emb38_run {s n : ℕ} {p : Machine 38 s} (C R index index' K pos pos' : ℕ) (left acc left' acc' : Poly)
    (ps : List Poly) (table : List Bool) (P : Poly) (stored : List Bool)
    (h : Step p n (SelectedPairFetch.H pos) (SelectedPairFetch.A C R index left acc ps table)
      (SelectedPairFetch.H pos') (SelectedPairFetch.A C R index' left' acc' ps table)) :
    Step (emb38 p) n (thrH pos) (thrA C R index K left acc ps table P stored)
      (thrH pos') (thrA C R index' K left' acc' ps table P stored) :=
  (((h.embed (fun _ : Fin 1 => 1) (fun _ => CompareMachine.word K)).embed (fun _ : Fin 2 => 0)
    (parkWords C R P)).embed (fun _ : Fin 1 => 0) (fun _ => stored))

theorem emb41_run {s n : ℕ} {p : Machine 41 s} (C R index index' K pos pos' : ℕ) (left acc left' acc' : Poly)
    (ps : List Poly) (table : List Bool) (P P' : Poly) (stored : List Bool)
    (h : Step p n (bodyH pos) (bodyA C R index K left acc ps table P)
      (bodyH pos') (bodyA C R index' K left' acc' ps table P')) :
    Step (emb41 p) n (thrH pos) (thrA C R index K left acc ps table P stored)
      (thrH pos') (thrA C R index' K left' acc' ps table P' stored) :=
  h.embed (fun _ : Fin 1 => 0) (fun _ => stored)

/-- Register copies inside the combine body, head cursor and index independent. -/
theorem copy_run' (C R index K pos : ℕ) (left acc : Poly) (ps : List Poly) (bits : List Bool) (P : Poly)
    (s1 t1 s2 t2 : Fin 41) (hne1 : s1 ≠ t1) (hne2 : s2 ≠ t2) (hsurv : s2 ≠ t1) (htgt : t2 ≠ t1)
    (hs1 : bodyH pos s1 = 0) (ht1 : bodyH pos t1 = 0) (hs2 : bodyH pos s2 = 0) (ht2 : bodyH pos t2 = 0)
    (l1 : (bodyA C R index K left acc ps bits P s1).length = R)
    (l2 : (bodyA C R index K left acc ps bits P t1).length = R)
    (l3 : (bodyA C R index K left acc ps bits P s2).length = R)
    (l4 : (bodyA C R index K left acc ps bits P t2).length = R) :
    Step (PhysicalCopyPair.machine (t := 41) 31 s1 t1 s2 t2) (4 * R + 5) (bodyH pos)
      (bodyA C R index K left acc ps bits P) (bodyH pos)
      (Function.update (Function.update (bodyA C R index K left acc ps bits P) t1
        (bodyA C R index K left acc ps bits P s1)) t2 (bodyA C R index K left acc ps bits P s2)) :=
  PhysicalCopyPair.run R 31 s1 t1 s2 t2 (bodyH pos) (bodyA C R index K left acc ps bits P)
    hne1 hne2 hsurv htgt rfl hs1 ht1 hs2 ht2 rfl l1 l2 l3 l4

/-- The index reload's bank update. -/
theorem thrA_reload (C R index K : ℕ) (left acc : Poly) (ps : List Poly) (table : List Bool) (P : Poly) :
    Function.update (thrA C R index K left acc ps table P (ZeroPadding.pad R (CompareMachine.word K))) 35
      (thrA C R index K left acc ps table P (ZeroPadding.pad R (CompareMachine.word K)) 41) =
    thrA C R K K left acc ps table P (ZeroPadding.pad R (CompareMachine.word K)) := by
  have e41 : thrA C R index K left acc ps table P (ZeroPadding.pad R (CompareMachine.word K)) 41 =
      ZeroPadding.pad R (CompareMachine.word K) := rfl
  rw [e41]
  unfold thrA
  have e35 : (35 : Fin 42) = (35 : Fin 41).castAdd 1 := rfl
  rw [e35, PhysicalAppendUpdate.left, bodyA_eq, bodyA_eq]
  have e35' : (35 : Fin 41) = (((35 : Fin 37).castAdd 1).castAdd 1).castAdd 2 := rfl
  rw [e35', update_inner]
  have h := OrderedPacketFold.update_index C R index K left acc ps
  unfold OrderedPacketStep.A at h
  rw [h]

/-! ## Machines of one code -/

noncomputable def moveM := emb38 SelectedFactorStep.move
noncomputable def initM := PhysicalBitCall.machine (37 : Fin 42) (emb41 (emb37 OrderedPacketReset.oneMachine))
noncomputable def reloadM := PhysicalIndexReload.machine (t := 42) 31 41 35
noncomputable def sweepThr := emb41 (TapeEmbedding.machine 2 sweepM)
noncomputable def addM := emb41 (emb37 OrderedPacketStep.add)

/-- One code of the THR combine. -/
noncomputable def thrBody := Composition.machine moveM (Composition.machine initM (Composition.machine reloadM
  (Composition.machine sweepThr (Composition.machine (emb41 copyAccLeft) (Composition.machine (emb41 copyParkAcc)
    (Composition.machine addM (Composition.machine (emb41 copyAccPark) (emb41 (emb37 OrderedPacketReset.zeroMachine)))))))))

def thrBodyBudget (C w K : ℕ) : ℕ :=
  1 + 1 + ((4 * commonReserve C w + 10 + 3) + 1 + ((2 * commonReserve C w + 6) + 1 +
    ((K * (fmulBudget C w + 3) + 3) + 1 + ((4 * commonReserve C w + 5) + 1 + ((4 * commonReserve C w + 5) + 1 +
      (ReusableArithmetic.boundedBudget C w + 1 + ((4 * commonReserve C w + 5) + 1 + (4 * commonReserve C w + 5))))))))

theorem word_pad_length (R k : ℕ) (hk : k + 1 ≤ R) : (ZeroPadding.pad R (CompareMachine.word k)).length = R := by
  rw [ZeroPadding.pad_length]
  simp [CompareMachine.word]
  omega

theorem sweepLeft_length (ps : List Poly) (bits : List Bool) (base K : ℕ) (left0 : Poly) (T : ℕ)
    (hl0 : left0.length ≤ T) (hps : ∀ P ∈ ps, P.length ≤ T) (n : ℕ) :
    (sweepLeft ps bits base K left0 n).length ≤ T := by
  induction n with
  | zero => exact hl0
  | succ n ih =>
    simp only [sweepLeft]
    split
    · by_cases h : K - (n + 1) < ps.length
      · rw [List.getD_eq_getElem _ _ h]
        exact hps _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ (by omega)]
        simp
    · exact ih

/-- **One code.** From table cursor `base+K+1` (block `[base, base+K]`), empty accumulator and
parked `P`: the code's term `T` (acceptance-initialized filtered product) is computed, `P` becomes
`add T P`, the accumulator is empty again, the cursor is at `base`, the index `0`, `left = T`. -/
theorem thrBody_run (C w : ℕ) (S : Finset ℕ) (d e : ℕ) (ps : List Poly) (table : List Bool)
    (base K : ℕ) (left P : Poly)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ Q ∈ ps, NormalizedIntermediate.Bounded S d Q)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfite : (S.card + 1) ^ e ≤ 2 ^ w)
    (hK : K ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hl : left.length ≤ 2 ^ w)
    (hsweep : ∀ n, n ≤ K → Fits C (sweepAcc ps table base K (initAcc table base K) n) ∧
      (sweepAcc ps table base K (initAcc table base K) n).length ≤ 2 ^ w)
    (hT : NormalizedIntermediate.Bounded S e (sweepAcc ps table base K (initAcc table base K) K))
    (hP : NormalizedIntermediate.Bounded S e P) (hw : 1 ≤ w) :
    Step thrBody (thrBodyBudget C w K) (thrH (base + K + 1))
      (thrA C (commonReserve C w) 0 K left [] ps table P (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K)))
      (thrH base)
      (thrA C (commonReserve C w) 0 K (sweepAcc ps table base K (initAcc table base K) K) [] ps table
        (Ring.add (sweepAcc ps table base K (initAcc table base K) K) P)
        (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K))) := by
  set R := commonReserve C w with hRdef
  set stored := ZeroPadding.pad R (CompareMachine.word K) with hstored
  set A0 := initAcc table base K with hA0
  set T := sweepAcc ps table base K A0 K with hTdef
  have hcap := OrderedPacketFold.driver_fit C w ps.length hN
  have hR1 : 1 ≤ R := by omega
  have hpsc : ∀ Q ∈ ps, Q.length ≤ 2 ^ w := fun Q hQ => (NormalizedIntermediate.census (hps Q hQ)).trans hfit
  have hTc : T.length ≤ 2 ^ w := (NormalizedIntermediate.census hT).trans hfite
  have hPc : P.length ≤ 2 ^ w := (NormalizedIntermediate.census hP).trans hfite
  have hTP : NormalizedIntermediate.Bounded S e (Ring.add T P) := NormalizedIntermediate.add hT hP
  have hTPc : (Ring.add T P).length ≤ 2 ^ w := (NormalizedIntermediate.census hTP).trans hfite
  set sL := sweepLeft ps table base K left K with hsL
  have hsLc : sL.length ≤ 2 ^ w := sweepLeft_length ps table base K left (2 ^ w) hl hpsc K
  -- 1. cursor onto the acceptance bit
  have s1 := emb38_run C R 0 0 K (base + K + 1) (base + K) left [] left [] ps table P stored
    (SelectedFactorStep.move_run C R 0 (base + K) left [] ps table)
  -- 2. acc := initAcc
  have s2 : Step initM (4 * R + 10 + 3) (thrH (base + K)) (thrA C R 0 K left [] ps table P stored)
      (thrH (base + K)) (thrA C R 0 K left A0 ps table P stored) := by
    cases hb : table.getD (base + K) false with
    | false =>
      have hb' : readTapeBit ((thrA C R 0 K left [] ps table P stored) 37) ((thrH (base + K)) 37) = false := hb
      have h := PhysicalBitCall.run_false (p := emb41 (emb37 OrderedPacketReset.oneMachine)) (37 : Fin 42)
        (thrH (base + K)) (thrA C R 0 K left [] ps table P stored) hb'
      have hA : A0 = [] := by rw [hA0]; unfold initAcc; rw [hb]; rfl
      rw [hA]
      exact h.enlarge (by omega)
    | true =>
      have hb' : readTapeBit ((thrA C R 0 K left [] ps table P stored) 37) ((thrH (base + K)) 37) = true := hb
      have call := emb41_run C R 0 0 K (base + K) (base + K) left [] left [[]] ps table P P stored
        (emb37_run C R 0 K (base + K) left [] left [[]] ps table P
          (OrderedPacketReset.one_run C w 0 left [] ps (by simp)))
      have h := PhysicalBitCall.run_true (37 : Fin 42) (p := emb41 (emb37 OrderedPacketReset.oneMachine)) hb' call
      have hA : A0 = [[]] := by rw [hA0]; unfold initAcc; rw [hb]; rfl
      rw [hA]
      exact h
  -- 3. index := K
  have s3 : Step reloadM (2 * R + 6) (thrH (base + K)) (thrA C R 0 K left A0 ps table P stored)
      (thrH (base + K)) (thrA C R K K left A0 ps table P stored) := by
    have h := PhysicalIndexReload.run R (31 : Fin 42) 41 35 (by decide) (by decide) (by decide)
      (thrH (base + K)) (thrA C R 0 K left A0 ps table P stored) rfl rfl rfl rfl
      (word_pad_length R K (by omega)) (word_pad_length R 0 (by omega))
    rw [hstored, thrA_reload] at h
    exact h
  -- 4. the filtered sweep
  have s4 := emb41_run C R K 0 K (base + K) base left A0 sL T ps table P P stored
    ((sweep_run C w S d ps table base K left A0 hS hps hfit hK hN hl hsweep hw).embed
      (fun _ : Fin 2 => 0) (parkWords C R P))
  -- 5. acc → left
  have s5 := emb41_run C R 0 0 K base base sL T T T ps table P P stored (by
    have h := copy_run' C R 0 K base sL T ps table P 26 25 27 28 (by decide) (by decide) (by decide)
      (by decide) rfl rfl rfl rfl (reg_lengths C w T hTc).1 (reg_lengths C w sL hsLc).1
      (reg_count_map C w T hTc) (reg_count_map C w sL hsLc)
    rw [bodyA_acc_to_left] at h
    exact h)
  -- 6. park → acc
  have s6 := emb41_run C R 0 0 K base base T T T P ps table P P stored (by
    have h := copy_run' C R 0 K base T T ps table P 39 26 40 27 (by decide) (by decide) (by decide)
      (by decide) rfl rfl rfl rfl (reg_lengths C w P hPc).1 (reg_lengths C w T hTc).1
      (reg_lengths C w P hPc).2 (reg_count_map C w T hTc)
    rw [bodyA_park_to_acc] at h
    exact h)
  -- 7. acc := add left acc
  have s7 := emb41_run C R 0 0 K base base T P T (Ring.add T P) ps table P P stored
    (emb37_run C R 0 K base T P T (Ring.add T P) ps table P
      (OrderedPacketStep.add_run C w 0 T P ps (SubstitutionCensus.fits_of_bounded C S hS hT)
        (SubstitutionCensus.fits_of_bounded C S hS hP) hT.1.1 hP.1.1 hTc hPc hw))
  -- 8. acc → park
  have s8 := emb41_run C R 0 0 K base base T (Ring.add T P) T (Ring.add T P) ps table P (Ring.add T P) stored (by
    have h := copy_run' C R 0 K base T (Ring.add T P) ps table P 26 39 27 40 (by decide) (by decide)
      (by decide) (by decide) rfl rfl rfl rfl (reg_lengths C w _ hTPc).1 (reg_lengths C w P hPc).1
      (reg_count_map C w _ hTPc) (reg_lengths C w P hPc).2
    rw [bodyA_acc_to_park] at h
    exact h)
  -- 9. acc := []
  have s9 := emb41_run C R 0 0 K base base T (Ring.add T P) T [] ps table (Ring.add T P) (Ring.add T P) stored
    (emb37_run C R 0 K base T (Ring.add T P) T [] ps table (Ring.add T P)
      (OrderedPacketReset.zero_run C w 0 T (Ring.add T P) ps hTPc))
  exact s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq s9)))))))

/-! ## The whole code loop -/

noncomputable def thrLoop := RepeatMachine.machine thrBody (fun _ _ => true)

/-- **The THR loop.** From table cursor `N*(K+1)`, empty accumulator and parked `[]`, the parked
register ends as the ordered parity `foldr add [] [term 0, …, term (N-1)]` of the codes' terms;
the cursor ends at `0`, the accumulator is empty, and bank, table, drivers and stored index word
are unchanged. -/
theorem thrLoop_run (C w : ℕ) (S : Finset ℕ) (d e : ℕ) (ps : List Poly) (table : List Bool)
    (N K : ℕ) (left0 : Poly)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ Q ∈ ps, NormalizedIntermediate.Bounded S d Q)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hfite : (S.card + 1) ^ e ≤ 2 ^ w)
    (hK : K ≤ ps.length) (hN : ps.length ≤ 2 ^ w) (hl0 : left0.length ≤ 2 ^ w)
    (hsweep : ∀ c, c < N → ∀ n, n ≤ K →
      Fits C (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n) ∧
      (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n).length ≤ 2 ^ w)
    (hterm : ∀ c, c < N → NormalizedIntermediate.Bounded S e (codeTerm ps table K c)) (hw : 1 ≤ w) :
    Step thrLoop (N * (thrBodyBudget C w K + 3) + 3)
      (Fin.addCases (m := 42) (n := 1) (motive := fun _ => ℕ) (thrH (N * (K + 1))) (fun _ => 1))
      (Fin.addCases (m := 42) (n := 1) (motive := fun _ => List Bool)
        (thrA C (commonReserve C w) 0 K left0 [] ps table []
          (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K))) (fun _ => CompareMachine.word N))
      (Fin.addCases (m := 42) (n := 1) (motive := fun _ => ℕ) (thrH 0) (fun _ => 1))
      (Fin.addCases (m := 42) (n := 1) (motive := fun _ => List Bool)
        (thrA C (commonReserve C w) 0 K (thrLeftAt ps table N K left0 N) [] ps table
          ((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add [])
          (ZeroPadding.pad (commonReserve C w) (CompareMachine.word K))) (fun _ => CompareMachine.word N)) := by
  set stored := ZeroPadding.pad (commonReserve C w) (CompareMachine.word K) with hstored
  let hs : ℕ → Fin 42 → ℕ := fun j => thrH ((N - j) * (K + 1))
  let as : ℕ → Fin 42 → List Bool := fun j => thrA C (commonReserve C w) 0 K
    (thrLeftAt ps table N K left0 j) [] ps table (thrParkAt ps table N K j) stored
  have body : ∀ j, j < N → Step thrBody (thrBodyBudget C w K) (hs j) (as j) (hs (j + 1)) (as (j + 1)) := by
    intro j hj
    have hleft : (thrLeftAt ps table N K left0 j).length ≤ 2 ^ w := by
      unfold thrLeftAt
      split
      · exact hl0
      · exact (NormalizedIntermediate.census (hterm _ (by omega))).trans hfite
    have hb := block_index N (K + 1) j hj
    have run := thrBody_run C w S d e ps table ((N - (j + 1)) * (K + 1)) K (thrLeftAt ps table N K left0 j)
      (thrParkAt ps table N K j) hS hps hfit hfite hK hN hleft (hsweep (N - (j + 1)) (by omega))
      (hterm (N - (j + 1)) (by omega)) (thrParkAt_bounded S e ps table N K j hterm) hw
    rw [show (N - (j + 1)) * (K + 1) + K + 1 = (N - (j + 1)) * (K + 1) + (K + 1) by omega, hb] at run
    have hl1 : thrLeftAt ps table N K left0 (j + 1) = codeTerm ps table K (N - (j + 1)) := by
      unfold thrLeftAt
      rw [if_neg (Nat.succ_ne_zero j)]
    dsimp only [hs, as]
    rw [hl1, thrParkAt_succ ps table N K j hj]
    exact run
  have result := PhysicalRepeatStep.run thrBody N (thrBodyBudget C w K) hs as body
  dsimp only [hs, as] at result
  rw [Nat.sub_zero, Nat.sub_self, Nat.zero_mul, thrParkAt_zero, thrParkAt_full] at result
  have h0 : thrLeftAt ps table N K left0 0 = left0 := by simp [thrLeftAt]
  rw [h0] at result
  exact result

end
end NearCubicWires.PacketsCombine
