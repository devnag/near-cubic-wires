import Proof.Packets.PacketsCombineThrDock2

/-! # P2 (iii): `ThrCombineStageK` — the THR combine stage (the modular radix row) at the kit seam

Consumer: `RowPolySplitK.thr` (`Proof/Packets/PacketsRowPolySplitKit.lean`), type `ThrCombineStageK Y K`: from the
digit coordinate vectors on tape 19 write the kit register of the THR row polynomial on tape 14, scratch
`Q3`, everything else kept. The row polynomial is `Normalized.structuralGF2ModularRadixRow p residue 2 coord`
(`PacketsRowPolyPlan.thr_rowPoly`, `rfl`). Paper: A.13.7 (`paper.tex:3113-3142`), charged in `T_prep`
(`paper.tex:1197-1200`); budget class: source-polynomial (`N = (pop+1)^digits ≤ tupleWork ≤ smallSize`).

`thrStage` builds the consumer's type from the metadata machine `ThrMeta` (hypothesis: templates and the
selection table `thrTableOf`), the capacity facts `ThrCap`, the reserve room `SymRoom`, room
`107 + M.extra ≤ Y.u3`, and a polynomial cost bound. ONE fixed machine: `thrLocalM M.machine` docked.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

/-! ## The local machine and its run -/

noncomputable def thrLocalM {e s : ℕ} (M : Machine (16 + e) s) :=
  Composition.machine (RecoveryFocus.machine (tmetaSlot e) M)
    (Composition.machine (RecoveryFocus.machine (tkbSlot e) KitBoot.machine)
      (Composition.machine (tmoves3 e)
        (Composition.machine (RecoveryFocus.machine (tengSlot e) thrLoop)
          (Composition.machine (PhysicalIndexReload.move (t := 118 + e) ⟨115, by omega⟩ .right)
            (RecoveryFocus.machine (tstoSlot e) symStore)))))

def thrLocalCost (mcost C w K N : ℕ) : ℕ :=
  mcost + 1 + (KitBoot.cost C w + 1 + ((1 + 1 + (1 + 1 + 1)) + 1 + ((N * (thrBodyBudget C w K + 3) + 3) + 1 +
    (1 + 1 + (2 * PacketBank.storeBudget (commonReserve C w) + 2)))))

/-- **The THR local run.** -/
theorem thrLocal_run {e s : ℕ} (M : Machine (16 + e) s) (mcost : ℕ) (mH : Fin (16 + e) → ℕ)
    (mA : Fin (16 + e) → List Bool) (Rb C w K N : ℕ) (input : List Bool) (keys : Fin 8 → List Bool)
    (coords table : List Bool)
    (hm : Step M mcost (fun _ => 0) (metaIn e input keys) mH mA)
    (hk : ∀ i : Fin (16 + e), i.val ≤ 8 → mA i = metaIn e input keys i ∧ mH i = 0)
    (h9 : mA ⟨9, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨9, by omega⟩ = 0)
    (h10 : mA ⟨10, by omega⟩ = UnaryTemplate.tape C ∧ mH ⟨10, by omega⟩ = 0)
    (h11 : mA ⟨11, by omega⟩ = UnaryTemplate.tape w ∧ mH ⟨11, by omega⟩ = 0)
    (h12 : mA ⟨12, by omega⟩ = UnaryTemplate.tape K ∧ mH ⟨12, by omega⟩ = 0)
    (h13 : mA ⟨13, by omega⟩ = UnaryTemplate.tape K ∧ mH ⟨13, by omega⟩ = 0)
    (h14 : mA ⟨14, by omega⟩ = UnaryTemplate.tape N ∧ mH ⟨14, by omega⟩ = 0)
    (h15 : mA ⟨15, by omega⟩ = table ∧ mH ⟨15, by omega⟩ = N * (K + 1))
    (S : Finset ℕ) (d : ℕ) (ps : List Poly)
    (hcoords : coords = OrderedPacketStep.bank C (commonReserve C w) ps)
    (hS : ∀ j ∈ S, j < C) (hps : ∀ Q ∈ ps, NormalizedIntermediate.Bounded S d Q)
    (hfit : (S.card + 1) ^ d ≤ 2 ^ w) (hK : K ≤ ps.length) (hN : ps.length ≤ 2 ^ w)
    (hsweep : ∀ c, c < N → ∀ n, n ≤ K →
      Fits C (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n) ∧
      (sweepAcc ps table (c * (K + 1)) K (initAcc table (c * (K + 1)) K) n).length ≤ 2 ^ w)
    (eD : ℕ) (hfitD : (S.card + 1) ^ eD ≤ 2 ^ w)
    (hterm : ∀ c, c < N → NormalizedIntermediate.Bounded S eD (codeTerm ps table K c)) (hw : 1 ≤ w)
    (hR1 : 1 ≤ commonReserve C w) (hRb : PacketBank.storeBudget (commonReserve C w) ≤ Rb)
    (hK2 : K + 2 ≤ Rb) (hN2 : N + 2 ≤ Rb) :
    ∃ (H' : Fin (118 + e) → ℕ) (A' : Fin (118 + e) → List Bool),
      Step (thrLocalM M) (thrLocalCost mcost C w K N) (fun _ => 0) (tlentry e Rb input keys coords) H' A' ∧
      (∀ i : Fin (118 + e), i.val ≤ 9 → A' i = tlentry e Rb input keys coords i ∧ H' i = 0) ∧
      A' ⟨10, by omega⟩ = ZeroPadding.pad Rb
        (ZeroPadding.pad (commonReserve C w)
            (((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add []).map (maskNat C)).flatten ++
          ZeroPadding.pad (commonReserve C w)
            (CompareMachine.word ((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add []).length)) ∧
      H' ⟨10, by omega⟩ = 0 := by
  have hRb' : commonReserve C w ≤ Rb := by unfold PacketBank.storeBudget at hRb; omega
  obtain ⟨H1, A1, s1, f1⟩ := tstage1 e Rb C w K N input keys coords table M mcost mH mA hm hk h9 h10 h11 h12 h13 h14 h15
  obtain ⟨H2, A2, s2, f2⟩ := tstage2 e Rb C w K N input keys coords table H1 A1 f1
  obtain ⟨H3, s3, f3⟩ := tstage3 e Rb C w K N input keys coords table H2 A2 f2
  obtain ⟨H4, A4, s4, o4, k4⟩ := tstage4 e Rb C w K N input keys coords table S d ps hcoords hS hps hfit
    hK hN hsweep eD hfitD hterm hw hR1 hRb' hK2 hN2 H3 A2 f3
  have f4 := tstage4_facts e Rb C w K N input keys coords table ps hcoords _ _ H3 A2 f3 H4 A4 o4 k4
  have hPf : ((List.ofFn (fun c : Fin N => codeTerm ps table K c.val)).foldr Ring.add []).length ≤ 2 ^ w := by
    have h := thrParkAt_bounded S eD ps table N K N hterm
    rw [thrParkAt_full] at h
    exact (NormalizedIntermediate.census h).trans hfitD
  obtain ⟨H6, A6, s6, fb6, fa6, fh6⟩ := tstage56 e Rb C w K input keys coords _ hPf hRb H4 A4 f4
  exact ⟨H6, A6, s1.seq (s2.seq (s3.seq (s4.seq s6))), fb6, fa6, fh6⟩

/-! ## The owed facts, typed -/

variable {a : DecompositionAlgorithm}

/-- **Capacity at every THR row** (the digit coordinate polynomials are kit operands at `K`). -/
def ThrCap (K : KitShape a) : Prop :=
  ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.ThrKey a r L target), k ∈ RCFive.RowKeys.thrKeys a r L target →
    ∃ (S : Finset ℕ) (d : ℕ), (∀ j ∈ S, j < K.C (.thr r four L target)) ∧
      (∀ P ∈ coordsListOf a (.thr r four L target) k, NormalizedIntermediate.Bounded S d P) ∧
      (S.card + 1) ^ d ≤ 2 ^ K.w (.thr r four L target) ∧
      (S.card + 1) ^ (d * thrD k) ≤ 2 ^ K.w (.thr r four L target) ∧
      thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1 ≤ 2 ^ K.w (.thr r four L target) ∧
      ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k + 1 ≤ 2 ^ K.w (.thr r four L target)

/-- Request-level upper bounds on the key's dimensions `K = digits*(pop+1)` and `N = (pop+1)^digits`
(both `≤` powers of `smallSize`: `digits < 2^walkLength ≤ smallSize`, `N ≤ tupleWork ≤ smallSize`). -/
def thrKmax (a : DecompositionAlgorithm) (r : Request) : ℕ := r.smallSize a * r.smallSize a

def thrNmax (a : DecompositionAlgorithm) (r : Request) : ℕ := r.smallSize a

/-- The stage's fuel at the request's largest key dimensions (monotone in `K`, `N`). -/
def thrStageCost (K : KitShape a) (M : ThrMeta a K) (r : Request) : ℕ :=
  thrLocalCost (M.cost r) (K.C r) (K.w r) (thrKmax a r) (thrNmax a r)

/-! ## The writer slot map: local `0 ↦ 0`, `1..8 ↦ 2..9`, `9 ↦ 19`, `10 ↦ 14`, `11.. ↦ Q3` -/

section Writer
variable {X : WriterShape a} (Y : RowPolyShape X) (e : ℕ) (hu : 107 + e ≤ Y.u3)

def twSlotVal (u12 i : ℕ) : ℕ :=
  if i = 0 then 0 else if i ≤ 8 then i + 1 else if i = 9 then 19 else if i = 10 then 14 else 10 + u12 + i

def twSlot (i : Fin (118 + e)) : Fin (10 + X.w) :=
  ⟨twSlotVal (Y.u1 + Y.u2) i.val, by
    have h := Y.hw1; have hi := i.isLt
    unfold twSlotVal WriterShape.w; split_ifs <;> omega⟩

theorem twSlot_injective : Function.Injective (twSlot Y e hu) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [twSlot, twSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem twSlot_Q3 (i : Fin (118 + e)) (hi : 11 ≤ i.val) : Y.inQ3 (twSlot Y e hu i) := by
  unfold RowPolyShape.inQ3
  simp only [twSlot, twSlotVal]
  split_ifs <;> omega

end Writer

/-! ## Row-level identities -/

theorem thr_coords_flat (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    coordsListOf a (.thr r four L target) k = (List.ofFn (fun digit : Fin (thrD k) =>
      List.ofFn (LiveRows.coordinatePoly true (thresholdFourfoldOccurrences r)
        (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
        (CloseoutFinalC10ThresholdRows.listDenominator a r target)
        (Finset.univ.filter (fun i =>
          (modularCoefficientResidue (ThresholdRows.equation a r k.selection) k.prime.val i).testBit digit.val))
        k.seed))).flatten := by
  show coordsList _ _ _ (thrMasks a r L target k) k.seed = _
  unfold coordsList thrMasks
  rw [flatMap_ofFn]
  rfl

theorem thr_coords_length (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    (coordsListOf a (.thr r four L target) k).length = thrD k * ((thresholdFourfoldOccurrences r).length + 1) := by
  rw [thr_coords_flat]
  exact flatten_ofFn_length _ (fun _ => List.length_ofFn)

theorem thr_poly_eq (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    (rcDecode a (.thr r four L target) k).polynomial =
      (List.ofFn (fun c : Fin (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k) =>
        codeTerm (coordsListOf a (.thr r four L target) k) (thrTableOf r L target k)
          (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) c.val)).foldr Ring.add [] := by
  rw [thr_rowPoly, thr_coords_flat]
  unfold thrTableOf
  exact (thr_value _ _ _).symm

/-- The writer's bank at the local slots is the local entry (heads `0`). -/
theorem thrStage_hin {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (e : ℕ) (hu : 107 + e ≤ Y.u3)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target)
    (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (hkept : ∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.thr r four L target) (some k) [] i ∧ H i = 0)
    (h19A : A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.thr r four L target))
      (coordWordK K (.thr r four L target) k))
    (h19H : H (Y.tape 19 (by omega)) = 0)
    (hblank : ∀ i : Fin (10 + X.w), Y.inQ3 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.thr r four L target)) false ∧ H i = 0)
    (i : Fin (118 + e)) :
    H (twSlot Y e hu i) = 0 ∧ A (twSlot Y e hu i) = tlentry e (X.R (.thr r four L target))
      (RepairOrdinary.frame (Request.input a (.thr r four L target))) (keyWord a (.thr r four L target) (some k))
      (coordWordK K (.thr r four L target) k) i := by
  by_cases h0 : i.val = 0
  · have ei : twSlot Y e hu i = ⟨0, by omega⟩ := Fin.ext (by simp [twSlot, twSlotVal, h0])
    rw [ei]
    refine ⟨(hkept _ (by simp) (by simp)).2, (hkept _ (by simp) (by simp)).1.trans ?_⟩
    refine (layout_bank_zero X (.thr r four L target) (some k : Option (rcKey a (.thr r four L target))) _).trans ?_
    unfold tlentry; rw [if_pos h0]
  by_cases h8 : i.val ≤ 8
  · have ei : twSlot Y e hu i = ⟨(i.val - 1) + 2, by have := Y.hw1; unfold WriterShape.w; omega⟩ :=
      Fin.ext (by simp [twSlot, twSlotVal, h0, h8]; omega)
    rw [ei]
    refine ⟨(hkept _ (by simp; omega) (by simp)).2, (hkept _ (by simp; omega) (by simp)).1.trans ?_⟩
    refine (layout_bank_key X (.thr r four L target) (some k : Option (rcKey a (.thr r four L target)))
      ⟨i.val - 1, by omega⟩ _).trans ?_
    unfold tlentry
    rw [if_neg h0, dif_pos ⟨by omega, h8⟩]
  by_cases h9 : i.val = 9
  · have ei : twSlot Y e hu i = Y.tape 19 (by omega) := Fin.ext (by
      simp [twSlot, twSlotVal, h9, RowPolyShape.tape])
    rw [ei, h19A, h19H]
    refine ⟨rfl, ?_⟩
    unfold tlentry
    rw [if_neg h0, dif_neg (by omega), if_pos h9]
  rw [tlentry_high _ _ _ _ _ i (by omega)]
  by_cases h10 : i.val = 10
  · have ei : twSlot Y e hu i = X.port 14 (by omega) := Fin.ext (by
      simp [twSlot, twSlotVal, h10, WriterShape.port])
    rw [ei, (hblank _ (Or.inr rfl)).1, (hblank _ (Or.inr rfl)).2, Dock.pad_nil_eq]
    exact ⟨rfl, rfl⟩
  · have hq := twSlot_Q3 Y e hu i (by omega)
    rw [(hblank _ (Or.inl hq)).1, (hblank _ (Or.inl hq)).2, Dock.pad_nil_eq]
    exact ⟨rfl, rfl⟩

theorem thrStage_run {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : ThrMeta a K)
    (hu : 107 + M.extra ≤ Y.u3) (cap : ThrCap K) (room : SymRoom X K)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) (hk : k ∈ RCFive.RowKeys.thrKeys a r L target)
    (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (hkept : ∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.thr r four L target) (some k) [] i ∧ H i = 0)
    (h19A : A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.thr r four L target))
      (coordWordK K (.thr r four L target) k))
    (h19H : H (Y.tape 19 (by omega)) = 0)
    (hblank : ∀ i : Fin (10 + X.w), Y.inQ3 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.thr r four L target)) false ∧ H i = 0) :
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step (RecoveryFocus.machine (twSlot Y M.extra hu) (thrLocalM M.machine))
        (thrLocalCost (M.cost (.thr r four L target)) (K.C (.thr r four L target)) (K.w (.thr r four L target))
          (thrD k * ((thresholdFourfoldOccurrences r).length + 1))
          (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k)) H A H' A' ∧
      A' (X.port 14 (by omega)) = ZeroPadding.pad (X.R (.thr r four L target))
        (rowPolyWordK K (.thr r four L target) k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ Y.inQ3 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i := by
  obtain ⟨mH, mA, hm, hk8, h9, h9h, h10, h10h, h11, h11h, h12, h12h, h13, h13h, h14, h14h, h15, h15h⟩ :=
    M.run r four L target k hk
  obtain ⟨S, d, hS, hps, hfit, hfitD, hKw, hNw⟩ := cap r four L target k hk
  have hlenps := thr_coords_length (a := a) r four L target k
  have hw := K.w_pos (.thr r four L target)
  have hres := reserve_ge (K.C (.thr r four L target)) (K.w (.thr r four L target)) hw
  have hroom := room (.thr r four L target)
  have hroom' := hroom
  unfold PacketBank.storeBudget at hroom'
  have hsw : ∀ c, c < ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k → ∀ n,
      n ≤ thrD k * ((thresholdFourfoldOccurrences r).length + 1) →
      NormalizedIntermediate.Bounded S (d * thrD k)
        (sweepAcc (coordsListOf a (.thr r four L target) k) (thrTableOf r L target k)
          (c * (thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1))
          (thrD k * ((thresholdFourfoldOccurrences r).length + 1))
          (initAcc (thrTableOf r L target k) (c * (thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1))
            (thrD k * ((thresholdFourfoldOccurrences r).length + 1))) n) := by
    intro c hc n _
    exact thr_sweep_bounded S d _ hps _ _ _ _ _ ⟨c, hc⟩ n
  obtain ⟨H1, A1, s1, fb1, fa1, fh1⟩ := thrLocal_run M.machine (M.cost (.thr r four L target)) mH mA
    (X.R (.thr r four L target)) (K.C (.thr r four L target)) (K.w (.thr r four L target))
    (thrD k * ((thresholdFourfoldOccurrences r).length + 1)) (((thresholdFourfoldOccurrences r).length + 1) ^ thrD k)
    (RepairOrdinary.frame (Request.input a (.thr r four L target))) (keyWord a (.thr r four L target) (some k))
    (coordWordK K (.thr r four L target) k) (thrTableOf r L target k) hm hk8 ⟨h9, h9h⟩ ⟨h10, h10h⟩
    ⟨h11, h11h⟩ ⟨h12, h12h⟩ ⟨h13, h13h⟩ ⟨h14, h14h⟩ ⟨h15, h15h⟩ S d (coordsListOf a (.thr r four L target) k)
    rfl hS hps hfit (le_of_eq hlenps.symm) (by rw [hlenps]; omega)
    (fun c hc n hn => ⟨SubstitutionCensus.fits_of_bounded _ S hS (hsw c hc n hn),
      (NormalizedIntermediate.census (hsw c hc n hn)).trans hfitD⟩)
    (d * thrD k) hfitD (fun c hc => hsw c hc _ (le_refl _)) hw (by omega) hroom (by omega) (by omega)
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift s1 (twSlot Y M.extra hu) (twSlot_injective Y M.extra hu) (fun _ => 0) H A
    (fun i => by
      rw [ZeroPadding.pad_zero]
      exact thrStage_hin Y K M.extra hu r four L target k H A hkept h19A h19H hblank i)
  have e14 : X.port 14 (by omega) = twSlot Y M.extra hu ⟨10, by omega⟩ :=
    Fin.ext (by simp [twSlot, twSlotVal, WriterShape.port])
  refine ⟨H', A', st, ?_, ?_, ?_⟩
  · rw [e14, (o _).2, ZeroPadding.pad_zero, fa1, rowPolyWord_eq, thr_poly_eq]
  · rw [e14, (o _).1, fh1]
  · intro i hq h14
    by_cases hex : ∃ j, twSlot Y M.extra hu j = i
    · obtain ⟨j, rfl⟩ := hex
      have hj : j.val ≤ 9 := by
        by_contra hc
        by_cases hj10 : j.val = 10
        · exact h14 (by simp [twSlot, twSlotVal, hj10])
        · exact hq (twSlot_Q3 Y M.extra hu j (by omega))
      have hin := thrStage_hin Y K M.extra hu r four L target k H A hkept h19A h19H hblank j
      rw [(o j).1, (o j).2, ZeroPadding.pad_zero, (fb1 j hj).1, (fb1 j hj).2, hin.1, hin.2]
      exact ⟨rfl, rfl⟩
    · have := kp i (fun j hj => hex ⟨j, hj⟩)
      exact ⟨this.2, this.1⟩

/-! ## Fuel monotonicity (the key's dimensions are bounded by the request's) -/

theorem thrBodyBudget_mono (C w K K' : ℕ) (h : K ≤ K') : thrBodyBudget C w K ≤ thrBodyBudget C w K' := by
  unfold thrBodyBudget
  have := Nat.mul_le_mul_right (fmulBudget C w + 3) h
  omega

theorem thrLocalCost_mono (mcost C w K N K' N' : ℕ) (hK : K ≤ K') (hN : N ≤ N') :
    thrLocalCost mcost C w K N ≤ thrLocalCost mcost C w K' N' := by
  unfold thrLocalCost
  have h1 := thrBodyBudget_mono C w K K' hK
  have h2 : N * (thrBodyBudget C w K + 3) ≤ N' * (thrBodyBudget C w K' + 3) :=
    Nat.mul_le_mul hN (by omega)
  omega

theorem thr_dims_le (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrD k * ((thresholdFourfoldOccurrences r).length + 1) ≤ thrKmax a (.thr r four L target) ∧
      ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k ≤ thrNmax a (.thr r four L target) := by
  have hp := (SupplierPrime.mem_primesUpTo.mp k.prime.property).2
  have hD : thrD k ≤ modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) := by
    unfold thrD modulusDigitCount
    exact Nat.succ_le_succ (Nat.log_mono_right hp)
  have hdig : thrD k < 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r target) :=
    thr_digits_lt a r L target k
  have hwalk := small_walk a (.thr r four L target)
  change 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r target) ≤ _ at hwalk
  have hocc := RCFive.PacketBounds.occurrence_power a (.thr r four L target)
  change ((thresholdFourfoldOccurrences r).length + 2) ^ _ ≤ _ at hocc
  have hpop : (thresholdFourfoldOccurrences r).length + 2 ≤ (Request.thr r four L target).smallSize a :=
    (Nat.le_self_pow (by omega) _).trans hocc
  have htw : Request.tupleWork a (.thr r four L target) + 1 ≤ (Request.thr r four L target).smallSize a := by
    dsimp only [Request.smallSize]
    generalize (2:ℕ) ^ (Packets.live ((Request.thr r four L target).family a)).card = livePower
    generalize (2:ℕ) ^ (canonicalWalkLength ((Request.thr r four L target).denominator a)) = walkPower
    omega
  refine ⟨Nat.mul_le_mul (by omega) (by omega), ?_⟩
  have hN : ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k ≤ Request.tupleWork a (.thr r four L target) := by
    show _ ≤ ((thresholdFourfoldOccurrences r).length + 1) ^
      modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target)
    exact Nat.pow_le_pow_right (by omega) hD
  show _ ≤ (Request.thr r four L target).smallSize a
  omega

/-- **The THR combine stage at the kit seam** (the consumer's exact type). -/
def thrStage {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : ThrMeta a K)
    (hu : 107 + M.extra ≤ Y.u3) (cap : ThrCap K) (room : SymRoom X K) (c d : ℕ)
    (hcost : ∀ r, thrStageCost K M r ≤ c * (r.smallSize a) ^ d) : ThrCombineStageK Y K where
  states := _
  machine := RecoveryFocus.machine (twSlot Y M.extra hu) (thrLocalM M.machine)
  cost := thrStageCost K M
  coefficient := c
  degree := d
  cost_le := hcost
  run := fun r four L target k hk H A hkept h19A h19H hblank => by
    obtain ⟨H', A', st, h14A, h14H, hframe⟩ :=
      thrStage_run Y K M hu cap room r four L target k hk H A hkept h19A h19H hblank
    have hd := thr_dims_le (a := a) r four L target k
    exact ⟨H', A', st.enlarge (thrLocalCost_mono _ _ _ _ _ _ _ hd.1 hd.2), h14A, h14H, hframe⟩

end
end NearCubicWires.PacketsCombine
