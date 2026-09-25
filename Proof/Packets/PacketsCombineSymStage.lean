import Proof.Packets.PacketsCombineSymLocalRun

/-! # P2 (ii): `SymCombineStageK` — the SYM combine stage at the kit seam

Consumer: `RowPolySplitK.sym` (`Proof/Packets/PacketsRowPolySplitKit.lean`), type `SymCombineStageK Y K`: from the
coordinate vectors on tape 19 (`pad R (coordWordK K r k)`) write the kit register of the SYM row
polynomial on tape 14 (`pad R (rowPolyWordK K r k)`), scratch `Q2`, everything else kept. The row
polynomial is `Normalized.structuralGF2FiniteConjunction (fun i => structuralGF2OneHotLookup …)`
(`PacketsRowPolyPlan.sym_rowPoly`, `rfl`). Paper: the row's canonical polynomial expansion is charged in
`T_prep` (`paper.tex:1197-1200`); budget class: source-polynomial.

`symStage` builds the consumer's type from: the metadata machine `SymMeta` (hypothesis, typed in
`PacketsCombineSymLocal`), the capacity facts `SymCap` (the coordinate polynomials' support/degree and
census at the kit parameters), the reserve room `SymRoom` (`8·R + 15 ≤` the writer's reserve), room
`106 + M.extra ≤ Y.u2` in `Q2`, and a polynomial cost bound. The machine is ONE fixed machine: the
local machine `symLocalM M.machine` docked into the writer's bank.
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

variable {a : DecompositionAlgorithm}

/-! ## The owed facts, typed -/

/-- **Capacity at every SYM row** (the coordinate polynomials are kit operands at `K`). -/
def SymCap (K : KitShape a) : Prop :=
  ∀ (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ)
    (k : RCFive.RowKeys.SymKey r L target), k ∈ RCFive.RowKeys.symKeys r L target →
    ∃ (S : Finset ℕ) (d : ℕ), (∀ j ∈ S, j < K.C (.sym r four L target)) ∧
      (∀ P ∈ coordsListOf a (.sym r four L target) k, NormalizedIntermediate.Bounded S d P) ∧
      (S.card + 1) ^ d ≤ 2 ^ K.w (.sym r four L target) ∧
      (S.card + 1) ^ (d * r.circuits.length) ≤ 2 ^ K.w (.sym r four L target) ∧
      r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1) + 1 ≤ 2 ^ K.w (.sym r four L target)

/-- **Room in the writer's reserve** for the kit reserve and the store. -/
def SymRoom (X : WriterShape a) (K : KitShape a) : Prop :=
  ∀ r, PacketBank.storeBudget (commonReserve (K.C r) (K.w r)) ≤ X.R r

/-- The SYM request dimensions (zero off SYM). -/
def symN : Request → ℕ
  | .sym r _ _ _ => r.circuits.length
  | _ => 0

def symM : Request → ℕ
  | .sym r _ _ _ => (symmetricFourfoldOccurrences r).length + 1
  | _ => 0

/-- The stage's fuel. -/
def symStageCost (K : KitShape a) (M : SymMeta a K) (r : Request) : ℕ :=
  symLocalCost (M.cost r) (K.C r) (K.w r) (symN r) (symM r)

/-! ## The writer slot map: local `0 ↦ 0`, `1..8 ↦ 2..9`, `9 ↦ 19`, `10 ↦ 14`, `11.. ↦ Q2` -/

section Writer
variable {X : WriterShape a} (Y : RowPolyShape X) (e : ℕ) (hu : 106 + e ≤ Y.u2)

def wSlotVal (u1 i : ℕ) : ℕ :=
  if i = 0 then 0 else if i ≤ 8 then i + 1 else if i = 9 then 19 else if i = 10 then 14 else 10 + u1 + i

def wSlot (i : Fin (117 + e)) : Fin (10 + X.w) :=
  ⟨wSlotVal Y.u1 i.val, by
    have h := Y.hw1; have hi := i.isLt
    unfold wSlotVal WriterShape.w; split_ifs <;> omega⟩

theorem wSlot_injective : Function.Injective (wSlot Y e hu) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [wSlot, wSlotVal] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem wSlot_Q2 (i : Fin (117 + e)) (hi : 11 ≤ i.val) : Y.inQ2 (wSlot Y e hu i) := by
  unfold RowPolyShape.inQ2
  simp only [wSlot, wSlotVal]
  split_ifs <;> omega

end Writer

/-! ## Row-level identities -/

theorem layout_bank_zero (X : WriterShape a) (r : Request) (c : Option (rcKey a r)) (h : 0 < 10 + X.w) :
    X.layout.bank r c [] ⟨0, h⟩ = RepairOrdinary.frame (Request.input a r) := by
  simp [Layout.bank, WriterShape.layout, digitLayout]

theorem layout_bank_key (X : WriterShape a) (r : Request) (c : Option (rcKey a r)) (f : Fin 8)
    (h : f.val + 2 < 10 + X.w) :
    X.layout.bank r c [] ⟨f.val + 2, h⟩ = keyWord a r c f := by
  have hf := f.isLt
  simp only [Layout.bank, WriterShape.layout, digitLayout, keyWord]
  rw [if_neg (by intro he; have := congrArg Fin.val he; simp at this)]
  simp only [show ¬ (10 ≤ f.val + 2) by omega, decide_false, Bool.false_eq_true, if_false,
    show 2 ≤ f.val + 2 ∧ f.val + 2 < 10 from ⟨by omega, by omega⟩, decide_true, if_true, dif_pos,
    and_self]
  congr 3

theorem flatMap_ofFn {α β : Type} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn f).flatMap g = (List.ofFn (fun i => g (f i))).flatten := by
  simp [List.flatMap, List.map_ofFn, Function.comp_def]

theorem sym_coords_flat (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) :
    coordsListOf a (.sym r four L target) k = (List.ofFn (fun i : Fin r.circuits.length =>
      List.ofFn (LiveRows.coordinatePoly true (symmetricFourfoldOccurrences r)
        (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)
        (symmetricCircuitMask r i) k.seed))).flatten := by
  show coordsList _ _ _ (symMasks r) k.seed = _
  unfold coordsList symMasks
  rw [flatMap_ofFn]

theorem sym_coords_length (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) :
    (coordsListOf a (.sym r four L target) k).length =
      r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1) := by
  rw [sym_coords_flat]
  exact flatten_ofFn_length _ (fun _ => List.length_ofFn)

theorem sym_poly_eq (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) :
    (rcDecode a (.sym r four L target) k).polynomial =
      Normalized.structuralGF2Product (blockPolys (coordsListOf a (.sym r four L target) k)
        (symBitsWord r L target k) r.circuits.length ((symmetricFourfoldOccurrences r).length + 1)) := by
  rw [sym_rowPoly, sym_coords_flat, symBitsWord, sym_value]

theorem rowPolyWord_eq (K : KitShape a) (r : Request) (k : rcKey a r) :
    rowPolyWordK K r k =
      ZeroPadding.pad (commonReserve (K.C r) (K.w r)) (((rcDecode a r k).polynomial).map (maskNat (K.C r))).flatten ++
      ZeroPadding.pad (commonReserve (K.C r) (K.w r)) (CompareMachine.word (rcDecode a r k).polynomial.length) := by
  unfold rowPolyWordK KitShape.word PolyKit.vector PacketVector.bank
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold PacketVector.entry PacketVector.payload PacketVector.count PolyKit.masks
  rw [List.length_map]
  rfl

/-! ## The stage -/

theorem reserve_ge (C w : ℕ) (hw : 1 ≤ w) : 65536 * (C + 1) ≤ commonReserve C w ∧ 2 * 2 ^ w ≤ commonReserve C w := by
  unfold commonReserve
  have h1 : C + 1 ≤ (C + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
  have h3 : 2 ^ w ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 1 ≤ (C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  constructor
  · calc 65536 * (C + 1) ≤ 65536 * (C + 1) ^ 4 * 1 := by nlinarith
      _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.mul_le_mul_left _ h2
  · calc 2 * 2 ^ w ≤ 65536 * 1 * 2 ^ (8 * w) := by omega
      _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := by
        apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ h4

/-- The writer's bank at the local slots is the local entry (heads `0`). -/
theorem symStage_hin {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (e : ℕ) (hu : 106 + e ≤ Y.u2)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target)
    (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (hkept : ∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.sym r four L target) (some k) [] i ∧ H i = 0)
    (h19A : A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.sym r four L target))
      (coordWordK K (.sym r four L target) k))
    (h19H : H (Y.tape 19 (by omega)) = 0)
    (hblank : ∀ i : Fin (10 + X.w), Y.inQ2 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.sym r four L target)) false ∧ H i = 0)
    (i : Fin (117 + e)) :
    H (wSlot Y e hu i) = 0 ∧ A (wSlot Y e hu i) = lentry e (X.R (.sym r four L target))
      (RepairOrdinary.frame (Request.input a (.sym r four L target))) (keyWord a (.sym r four L target) (some k))
      (coordWordK K (.sym r four L target) k) i := by
  by_cases h0 : i.val = 0
  · have ei : wSlot Y e hu i = ⟨0, by omega⟩ := Fin.ext (by simp [wSlot, wSlotVal, h0])
    rw [ei]
    refine ⟨(hkept _ (by simp) (by simp)).2, (hkept _ (by simp) (by simp)).1.trans ?_⟩
    refine (layout_bank_zero X (.sym r four L target) (some k : Option (rcKey a (.sym r four L target))) _).trans ?_
    unfold lentry; rw [if_pos h0]
  by_cases h8 : i.val ≤ 8
  · have ei : wSlot Y e hu i = ⟨(i.val - 1) + 2, by have := Y.hw1; unfold WriterShape.w; omega⟩ :=
      Fin.ext (by simp [wSlot, wSlotVal, h0, h8]; omega)
    rw [ei]
    refine ⟨(hkept _ (by simp; omega) (by simp)).2, (hkept _ (by simp; omega) (by simp)).1.trans ?_⟩
    refine (layout_bank_key X (.sym r four L target) (some k : Option (rcKey a (.sym r four L target)))
      ⟨i.val - 1, by omega⟩ _).trans ?_
    unfold lentry
    rw [if_neg h0, dif_pos ⟨by omega, h8⟩]
  by_cases h9 : i.val = 9
  · have ei : wSlot Y e hu i = Y.tape 19 (by omega) := Fin.ext (by
      simp [wSlot, wSlotVal, h9, RowPolyShape.tape])
    rw [ei, h19A, h19H]
    refine ⟨rfl, ?_⟩
    unfold lentry
    rw [if_neg h0, dif_neg (by omega), if_pos h9]
  rw [lentry_high _ _ _ _ _ i (by omega)]
  by_cases h10 : i.val = 10
  · have ei : wSlot Y e hu i = X.port 14 (by omega) := Fin.ext (by
      simp [wSlot, wSlotVal, h10, WriterShape.port])
    rw [ei, (hblank _ (Or.inr rfl)).1, (hblank _ (Or.inr rfl)).2, Dock.pad_nil_eq]
    exact ⟨rfl, rfl⟩
  · have hq := wSlot_Q2 Y e hu i (by omega)
    rw [(hblank _ (Or.inl hq)).1, (hblank _ (Or.inl hq)).2, Dock.pad_nil_eq]
    exact ⟨rfl, rfl⟩

theorem symStage_run {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : SymMeta a K)
    (hu : 106 + M.extra ≤ Y.u2) (cap : SymCap K) (room : SymRoom X K)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4)
    (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ RCFive.RowKeys.symKeys r L target)
    (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (hkept : ∀ i : Fin (10 + X.w), i.val < 10 → i.val ≠ 1 →
      A i = X.layout.bank (.sym r four L target) (some k) [] i ∧ H i = 0)
    (h19A : A (Y.tape 19 (by omega)) = ZeroPadding.pad (X.R (.sym r four L target))
      (coordWordK K (.sym r four L target) k))
    (h19H : H (Y.tape 19 (by omega)) = 0)
    (hblank : ∀ i : Fin (10 + X.w), Y.inQ2 i ∨ i.val = 14 →
      A i = List.replicate (X.R (.sym r four L target)) false ∧ H i = 0) :
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step (RecoveryFocus.machine (wSlot Y M.extra hu) (symLocalM M.machine))
        (symStageCost K M (.sym r four L target)) H A H' A' ∧
      A' (X.port 14 (by omega)) = ZeroPadding.pad (X.R (.sym r four L target))
        (rowPolyWordK K (.sym r four L target) k) ∧
      H' (X.port 14 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ Y.inQ2 i → i.val ≠ 14 → A' i = A i ∧ H' i = H i := by
  obtain ⟨mH, mA, hm, hk8, h9, h9h, h10, h10h, h11, h11h, h12, h12h, h13, h13h, h14, h14h, h15, h15h⟩ :=
    M.run r four L target k hk
  obtain ⟨S, d, hS, hps, hfit, hfitn, hN'⟩ := cap r four L target k hk
  have hlenps := sym_coords_length (a := a) r four L target k
  have hw := K.w_pos (.sym r four L target)
  have hres := reserve_ge (K.C (.sym r four L target)) (K.w (.sym r four L target)) hw
  have hpop : (symmetricFourfoldOccurrences r).length + 1 ≤ K.C (.sym r four L target) := by
    have h := K.codes (.sym r four L target)
    have h2 : ((Request.sym r four L target).family a).occurrences.length + 1 ≤ codeNeed a (.sym r four L target) := by
      unfold codeNeed; omega
    exact (show (symmetricFourfoldOccurrences r).length + 1 ≤ codeNeed a (.sym r four L target) from h2).trans h
  have hroom := room (.sym r four L target)
  have hroom' := hroom
  unfold PacketBank.storeBudget at hroom'
  obtain ⟨H1, A1, s1, fb1, fa1, fh1⟩ := symLocal_run M.machine (M.cost (.sym r four L target)) mH mA
    (X.R (.sym r four L target)) (K.C (.sym r four L target)) (K.w (.sym r four L target))
    ((symmetricFourfoldOccurrences r).length + 1) r.circuits.length
    (RepairOrdinary.frame (Request.input a (.sym r four L target))) (keyWord a (.sym r four L target) (some k))
    (coordWordK K (.sym r four L target) k) (symBitsWord r L target k) hm hk8 ⟨h9, h9h⟩ ⟨h10, h10h⟩
    ⟨h11, h11h⟩ ⟨h12, h12h⟩ ⟨h13, h13h⟩ ⟨h14, h14h⟩ ⟨h15, h15h⟩ S d (coordsListOf a (.sym r four L target) k)
    rfl hS hps hfit hfitn (le_of_eq hlenps.symm) (by rw [hlenps]; omega) hw (by omega) hroom
    (by omega) (by omega) (by omega)
  obtain ⟨H', A', st, o, kp⟩ := Dock.lift s1 (wSlot Y M.extra hu) (wSlot_injective Y M.extra hu) (fun _ => 0) H A
    (fun i => by
      rw [ZeroPadding.pad_zero]
      exact symStage_hin Y K M.extra hu r four L target k H A hkept h19A h19H hblank i)
  have e14 : X.port 14 (by omega) = wSlot Y M.extra hu ⟨10, by omega⟩ :=
    Fin.ext (by simp [wSlot, wSlotVal, WriterShape.port])
  refine ⟨H', A', st, ?_, ?_, ?_⟩
  · rw [e14, (o _).2, ZeroPadding.pad_zero, fa1, rowPolyWord_eq, sym_poly_eq]
  · rw [e14, (o _).1, fh1]
  · intro i hq h14
    by_cases hex : ∃ j, wSlot Y M.extra hu j = i
    · obtain ⟨j, rfl⟩ := hex
      have hj : j.val ≤ 9 := by
        by_contra hc
        by_cases hj10 : j.val = 10
        · exact h14 (by simp [wSlot, wSlotVal, hj10])
        · exact hq (wSlot_Q2 Y M.extra hu j (by omega))
      have hin := symStage_hin Y K M.extra hu r four L target k H A hkept h19A h19H hblank j
      rw [(o j).1, (o j).2, ZeroPadding.pad_zero, (fb1 j hj).1, (fb1 j hj).2, hin.1, hin.2]
      exact ⟨rfl, rfl⟩
    · have := kp i (fun j hj => hex ⟨j, hj⟩)
      exact ⟨this.2, this.1⟩

/-- **The SYM combine stage at the kit seam** (the consumer's exact type). -/
def symStage {X : WriterShape a} (Y : RowPolyShape X) (K : KitShape a) (M : SymMeta a K)
    (hu : 106 + M.extra ≤ Y.u2) (cap : SymCap K) (room : SymRoom X K) (c d : ℕ)
    (hcost : ∀ r, symStageCost K M r ≤ c * (r.smallSize a) ^ d) : SymCombineStageK Y K where
  states := _
  machine := RecoveryFocus.machine (wSlot Y M.extra hu) (symLocalM M.machine)
  cost := symStageCost K M
  coefficient := c
  degree := d
  cost_le := hcost
  run := fun r four L target k hk H A hkept h19A h19H hblank =>
    symStage_run Y K M hu cap room r four L target k hk H A hkept h19A h19H hblank

end
end NearCubicWires.PacketsCombine
