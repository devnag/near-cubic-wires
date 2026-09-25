import Proof.Packets.PacketsWriterPlanKit
import Proof.Packets.PacketsLowerFacts
import Proof.Packets.PacketsLowerCost
import Proof.Packets.PacketsLowerTail

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.LowerKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

variable {a : DecompositionAlgorithm}

/-- The request's pool (live set, occurrences). -/
abbrev pool (a : DecompositionAlgorithm) (r : Request) :=
  CloseoutRowsUniversal.pool (Packets.live (r.family a)) (r.family a).occurrences

structure LowerMeta (a : DecompositionAlgorithm) (K : KitShape a) where
  tapes : ℕ
  tapes_ge : 7 ≤ tapes
  states : ℕ
  machine : Machine tapes states
  cost : Request → ℕ
  cM : ℕ
  dM : ℕ
  cost_le : ∀ r, cost r ≤ cM * (r.smallSize a) ^ dM
  cap : Request → ℕ
  cK : ℕ
  dK : ℕ
  cap_le : ∀ r, cap r ≤ cK * (r.smallSize a) ^ dK
  cap_ge : ∀ r, 64 * (ExtDecompositionBatch.B a (pool a r) + 2) ^ 2 ≤ cap r
  run : ∀ r, ∃ (H : Fin tapes → ℕ) (A : Fin tapes → List Bool),
    Step machine (cost r) (fun _ => 0)
      (fun i => if i.val = 0 then RepairOrdinary.frame (Request.input a r) else []) H A ∧
    A ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H ⟨0, by omega⟩ = 0 ∧
    A ⟨1, by omega⟩ = UnaryTemplate.tape (K.C r) ∧ H ⟨1, by omega⟩ = 0 ∧
    A ⟨2, by omega⟩ = UnaryTemplate.tape (K.C r) ∧ H ⟨2, by omega⟩ = 0 ∧
    A ⟨3, by omega⟩ = UnaryTemplate.tape (K.w r) ∧ H ⟨3, by omega⟩ = 0 ∧
    A ⟨4, by omega⟩ = UnaryTemplate.tape (r.family a).occurrences.length ∧ H ⟨4, by omega⟩ = 0 ∧
    A ⟨5, by omega⟩ = List.replicate (cap r) true ∧ H ⟨5, by omega⟩ = 0 ∧
    A ⟨6, by omega⟩ = CloseoutRowsRawAtomMeaning.countWord a (pool a r) ∧ H ⟨6, by omega⟩ = 0

/-- **The room** of F2's padded world inside the writer's scratch. -/
structure LowerFit (X : WriterShape a) (K : KitShape a) (m : LowerMeta a K) : Prop where
  width : 299 + (m.tapes - 7) ≤ X.w2
  cap : ∀ r, m.cap r + 1 ≤ X.R r
  log : ∀ r, CloseoutRowsRawAtomProducer.budget (m.cap r) (pool a r).length ≤ X.R r
  reserve : ∀ r, 2 * PolyKit.reserve (K.C r) (K.w r) ≤ X.R r
  pop : ∀ r, (r.family a).occurrences.length + 2 ≤ X.R r

/-! ## The core's dock -/

def slots (X : WriterShape a) (hw : 299 ≤ X.w2) (j : Fin 302) : Fin (10 + X.w) :=
  if j.val = 0 then ⟨0, by unfold WriterShape.w; omega⟩
  else if j.val = 1 then ⟨14, by unfold WriterShape.w; omega⟩
  else if j.val = 2 then ⟨10, by unfold WriterShape.w; omega⟩
  else ⟨19 + X.w1 + (j.val - 3), by have := j.isLt; unfold WriterShape.w; omega⟩

theorem slots_val (X : WriterShape a) (hw : 299 ≤ X.w2) (j : Fin 302) : (slots X hw j).val =
    if j.val = 0 then 0 else if j.val = 1 then 14 else if j.val = 2 then 10 else 19 + X.w1 + (j.val - 3) := by
  unfold slots; split_ifs <;> rfl

theorem slots_injective (X : WriterShape a) (hw : 299 ≤ X.w2) : Function.Injective (slots X hw) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [slots_val, slots_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem slots_P2 (X : WriterShape a) (hw : 299 ≤ X.w2) (j : Fin 302) (h : 3 ≤ j.val) : X.inP2 (slots X hw j) := by
  unfold WriterShape.inP2
  rw [slots_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have := j.isLt
  omega

/-! ## The metadata's dock -/

def metaAmb (X : WriterShape a) (T : ℕ) (hw : 299 + (T - 7) ≤ X.w2) (j : Fin T) : Fin (10 + X.w) :=
  if j.val = 0 then ⟨0, by unfold WriterShape.w; omega⟩
  else if h6 : j.val ≤ 6 then ⟨19 + X.w1 + (j.val - 1), by unfold WriterShape.w; omega⟩
  else ⟨19 + X.w1 + 299 + (j.val - 7), by have := j.isLt; unfold WriterShape.w; omega⟩

theorem metaAmb_val (X : WriterShape a) (T : ℕ) (hw : 299 + (T - 7) ≤ X.w2) (j : Fin T) :
    (metaAmb X T hw j).val =
      if j.val = 0 then 0 else if j.val ≤ 6 then 19 + X.w1 + (j.val - 1) else 19 + X.w1 + 299 + (j.val - 7) := by
  unfold metaAmb; split_ifs <;> rfl

theorem metaAmb_injective (X : WriterShape a) (T : ℕ) (hw : 299 + (T - 7) ≤ X.w2) :
    Function.Injective (metaAmb X T hw) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [metaAmb_val, metaAmb_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem metaAmb_P2 (X : WriterShape a) (T : ℕ) (hw : 299 + (T - 7) ≤ X.w2) (j : Fin T) (h : j.val ≠ 0) :
    X.inP2 (metaAmb X T hw j) := by
  unfold WriterShape.inP2
  rw [metaAmb_val, if_neg h]
  have := j.isLt
  split_ifs <;> omega

theorem hw_core {X : WriterShape a} {T : ℕ} (hw : 299 + (T - 7) ≤ X.w2) : 299 ≤ X.w2 := by omega

def machine (X : WriterShape a) {K : KitShape a} (m : LowerMeta a K) (hw : 299 + (m.tapes - 7) ≤ X.w2) :=
  Composition.machine (RecoveryFocus.machine (metaAmb X m.tapes hw) m.machine)
    (RecoveryFocus.machine (slots X (hw_core hw)) LowerCore.tailMachine)

/-- The request-level fuel. -/
def cost (K : KitShape a) (m : LowerMeta a K) (r : Request) : ℕ :=
  LowerCost.total (m.cost r) (K.C r) (K.w r) (m.cap r) (pool a r).length

/-! ## The run -/

theorem run (X : WriterShape a) (K : KitShape a) (m : LowerMeta a K) (fit : LowerFit X K m)
    (r : Request) (k : rcKey a r) (hk : k ∈ rcKeys a r) (H : Fin (10 + X.w) → ℕ) (A : Fin (10 + X.w) → List Bool)
    (h0A : A (X.port 0 (by omega)) = RepairOrdinary.frame (Request.input a r)) (h0H : H (X.port 0 (by omega)) = 0)
    (h14A : A (X.port 14 (by omega)) = ZeroPadding.pad (X.R r) (rowPolyWordK K r k))
    (h14H : H (X.port 14 (by omega)) = 0)
    (hblank : ∀ i : Fin (10 + X.w), X.inP2 i ∨ i.val = 10 → A i = List.replicate (X.R r) false ∧ H i = 0) :
    ∃ (H' : Fin (10 + X.w) → ℕ) (A' : Fin (10 + X.w) → List Bool),
      Step (machine X m fit.width) (cost K m r) H A H' A' ∧
      A' (X.port 10 (by omega)) = ZeroPadding.pad (X.R r)
        (ExtIncidence.stream (Packets.lowered a (r.family a) (rcDecode a r k)).reverse) ∧
      H' (X.port 10 (by omega)) = 0 ∧
      ∀ i : Fin (10 + X.w), ¬ X.inP2 i → i.val ≠ 10 → A' i = A i ∧ H' i = H i := by
  have ht := m.tapes_ge
  have hw := fit.width
  have hwc := hw_core hw
  obtain ⟨mH, mA, hm, e0, g0, e1, g1, e2, g2, e3, g3, e4, g4, e5, g5, e6, g6⟩ := m.run r
  have hword := LowerFacts.row_word K r k
  have hblank' : ∀ i : Fin (10 + X.w), X.inP2 i ∨ i.val = 10 →
      A i = ZeroPadding.pad (X.R r) [] ∧ H i = 0 := by
    intro i hi
    rw [Dock.pad_nil_eq]
    exact hblank i hi
  -- the metadata, docked
  obtain ⟨H1, A1, st1, o1, k1⟩ := Dock.lift hm (metaAmb X m.tapes hw) (metaAmb_injective X m.tapes hw)
    (fun j => if j.val = 0 then 0 else X.R r) H A (by
      intro j
      by_cases j0 : j.val = 0
      · have hs : metaAmb X m.tapes hw j = X.port 0 (by omega) := by
          apply Fin.ext; rw [metaAmb_val, if_pos j0]; rfl
        rw [hs, h0H, h0A, if_pos j0, if_pos j0, ZeroPadding.pad_zero]
        exact ⟨rfl, rfl⟩
      · obtain ⟨hA, hH⟩ := hblank' _ (Or.inl (metaAmb_P2 X m.tapes hw j j0))
        rw [hA, hH, if_neg j0, if_neg j0]
        exact ⟨rfl, rfl⟩)
  -- where the metadata's outputs sit, in core-local coordinates
  have mo : ∀ (n : ℕ) (hn : n < m.tapes) (_h1 : 1 ≤ n) (_h6 : n ≤ 6) (i : Fin 302), i.val = 2 + n →
      A1 (slots X hwc i) = ZeroPadding.pad (X.R r) (mA ⟨n, hn⟩) ∧
        H1 (slots X hwc i) = mH ⟨n, hn⟩ := by
    intro n hn h1 h6 i hi
    have e : slots X hwc i = metaAmb X m.tapes hw ⟨n, hn⟩ := by
      apply Fin.ext
      rw [slots_val, metaAmb_val]
      simp only
      split_ifs <;> omega
    rw [e, (o1 ⟨n, hn⟩).1, (o1 ⟨n, hn⟩).2]
    have hne : ¬ ((⟨n, hn⟩ : Fin m.tapes).val = 0) := by show ¬ n = 0; omega
    rw [if_neg hne]
    exact ⟨rfl, rfl⟩
  have notMeta : ∀ i : Fin (10 + X.w), (i.val = 10 ∨ i.val = 14 ∨
      (19 + X.w1 + 6 ≤ i.val ∧ i.val < 19 + X.w1 + 299)) → ∀ j, metaAmb X m.tapes hw j ≠ i := by
    intro i hi j hj
    have hv := congrArg Fin.val hj
    rw [metaAmb_val] at hv
    split_ifs at hv <;> omega
  have hport0 : metaAmb X m.tapes hw ⟨0, by omega⟩ = X.port 0 (by omega) := by
    apply Fin.ext; rw [metaAmb_val]; rfl
  have o10 := o1 ⟨0, by omega⟩
  rw [hport0] at o10
  simp only [if_true, ZeroPadding.pad_zero] at o10
  -- the core's entry state
  have f1 : LowerCore.Facts1 (X.R r) (K.C r) (K.w r) (r.family a).occurrences.length (m.cap r)
      (RepairOrdinary.frame (Request.input a r))
      (PacketVector.entry (PolyKit.reserve (K.C r) (K.w r))
        ((rcDecode a r k).polynomial.map (NormalizedFiniteTransport.maskNat (K.C r))))
      (CloseoutRowsRawAtomMeaning.countWord a (pool a r))
      (fun j => H1 (slots X hwc j)) (fun j => A1 (slots X hwc j)) := by
    have s0 : slots X hwc 0 = X.port 0 (by omega) := by apply Fin.ext; rw [slots_val]; rfl
    have s1 : slots X hwc 1 = X.port 14 (by omega) := by apply Fin.ext; rw [slots_val]; rfl
    have s2 : slots X hwc 2 = X.port 10 (by omega) := by apply Fin.ext; rw [slots_val]; rfl
    have k14 := k1 (X.port 14 (by omega)) (notMeta _ (Or.inr (Or.inl rfl)))
    have k10 := k1 (X.port 10 (by omega)) (notMeta _ (Or.inl rfl))
    obtain ⟨b10A, b10H⟩ := hblank' (X.port 10 (by omega)) (Or.inr rfl)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show A1 (slots X hwc 0) = _; rw [s0, o10.2, e0]
    · show H1 (slots X hwc 0) = 0; rw [s0, o10.1, g0]
    · show A1 (slots X hwc 1) = _; rw [s1, k14.2, h14A, hword]
    · show H1 (slots X hwc 1) = 0; rw [s1, k14.1, h14H]
    · show A1 (slots X hwc 2) = _; rw [s2, k10.2, b10A]
    · show H1 (slots X hwc 2) = 0; rw [s2, k10.1, b10H]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show A1 (slots X hwc 3) = _; rw [(mo 1 (by omega) (by omega) (by omega) 3 rfl).1, e1]
    · show H1 (slots X hwc 3) = 0; rw [(mo 1 (by omega) (by omega) (by omega) 3 rfl).2, g1]
    · show A1 (slots X hwc 4) = _; rw [(mo 2 (by omega) (by omega) (by omega) 4 rfl).1, e2]
    · show H1 (slots X hwc 4) = 0; rw [(mo 2 (by omega) (by omega) (by omega) 4 rfl).2, g2]
    · show A1 (slots X hwc 5) = _; rw [(mo 3 (by omega) (by omega) (by omega) 5 rfl).1, e3]
    · show H1 (slots X hwc 5) = 0; rw [(mo 3 (by omega) (by omega) (by omega) 5 rfl).2, g3]
    · show A1 (slots X hwc 6) = _; rw [(mo 4 (by omega) (by omega) (by omega) 6 rfl).1, e4]
    · show H1 (slots X hwc 6) = 0; rw [(mo 4 (by omega) (by omega) (by omega) 6 rfl).2, g4]
    · show A1 (slots X hwc 7) = _; rw [(mo 5 (by omega) (by omega) (by omega) 7 rfl).1, e5]
    · show H1 (slots X hwc 7) = 0; rw [(mo 5 (by omega) (by omega) (by omega) 7 rfl).2, g5]
    · show A1 (slots X hwc 8) = _; rw [(mo 6 (by omega) (by omega) (by omega) 8 rfl).1, e6]
    · show H1 (slots X hwc 8) = 0; rw [(mo 6 (by omega) (by omega) (by omega) 8 rfl).2, g6]
    · intro i hi
      have hv := slots_val X hwc i
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hv
      have hlt := i.isLt
      have kk := k1 (slots X hwc i) (notMeta _ (Or.inr (Or.inr (by omega))))
      obtain ⟨bA, bH⟩ := hblank' (slots X hwc i) (Or.inl (slots_P2 X hwc i (by omega)))
      exact ⟨kk.2.trans bA, kk.1.trans bH⟩
  -- the core's tail, from that state
  obtain ⟨Hc, Ac, sc, c0, d0, c1, d1, c2, d2⟩ := LowerCore.tail_run a (r.family a) (rcDecode a r k)
    (X.R r) (K.C r) (K.w r) (m.cap r) (RepairOrdinary.frame (Request.input a r)) _ _ f1
    (LowerFacts.one_le K r) (LowerFacts.pop_le K r) (LowerFacts.child_le K r) (K.w_pos r)
    (LowerFacts.fit_child K r k hk) (LowerFacts.fit_atom K r) (LowerFacts.row_kit_good K r k)
    (RowGood.row_degree a r k) (LowerFacts.row_census K r k hk) (m.cap_ge r) (fit.cap r) (fit.log r)
    (LowerFacts.row_fits K r k hk) (fit.reserve r) (fit.pop r)
  obtain ⟨H', A', st2, o2, k2⟩ := Dock.lift sc (slots X hwc) (slots_injective X hwc) (fun _ => 0) H1 A1 (by
    intro j
    rw [ZeroPadding.pad_zero]
    exact ⟨rfl, rfl⟩)
  have hcost : LowerCore.cost (m.cost r) (K.C r) (K.w r) (m.cap r) (pool a r).length
      (r.family a).occurrences.length (rcDecode a r k).polynomial (Packets.lowered a (r.family a) (rcDecode a r k)) ≤
      cost K m r :=
    LowerCost.core_cost_le _ _ _ _ _ _ _ _ (LowerFacts.pop_le K r) (K.w_pos r) (LowerFacts.row_census K r k hk)
      (LowerFacts.lowered_census K r k hk) (LowerFacts.norm_census K r k hk)
  rw [LowerCore.cost_split] at hcost
  have s2 : slots X hwc 2 = X.port 10 (by omega) := by apply Fin.ext; rw [slots_val]; rfl
  refine ⟨H', A', (st1.seq st2).enlarge hcost, ?_, ?_, ?_⟩
  · rw [← s2, (o2 2).2, ZeroPadding.pad_zero, c2, LowerFacts.norm_lowered]
  · rw [← s2, (o2 2).1, d2]
  · intro i hP h10
    by_cases i0 : i.val = 0
    · have hs : i = slots X hwc 0 := by apply Fin.ext; rw [slots_val]; simpa using i0
      have hp : i = X.port 0 (by omega) := Fin.ext i0
      rw [hs, (o2 0).1, (o2 0).2, ZeroPadding.pad_zero, c0, d0, ← hs, hp, h0A, h0H]
      exact ⟨rfl, rfl⟩
    by_cases i14 : i.val = 14
    · have hs : i = slots X hwc 1 := by apply Fin.ext; rw [slots_val]; simpa using i14
      have hp : i = X.port 14 (by omega) := Fin.ext i14
      rw [hs, (o2 1).1, (o2 1).2, ZeroPadding.pad_zero, c1, d1, ← hs, hp, h14A, h14H, hword]
      exact ⟨rfl, rfl⟩
    have nslot : ∀ j, slots X hwc j ≠ i := by
      intro j hj
      by_cases h3 : 3 ≤ j.val
      · exact hP (hj ▸ slots_P2 X hwc j h3)
      · have hv := congrArg Fin.val hj
        rw [slots_val] at hv
        split_ifs at hv <;> omega
    have nmeta : ∀ j, metaAmb X m.tapes hw j ≠ i := by
      intro j hj
      by_cases j0 : j.val = 0
      · have hv := congrArg Fin.val hj
        rw [metaAmb_val, if_pos j0] at hv
        exact i0 hv.symm
      · exact hP (hj ▸ metaAmb_P2 X m.tapes hw j j0)
    have q2 := k2 i nslot
    have q1 := k1 i nmeta
    exact ⟨q2.2.trans q1.2, q2.1.trans q1.1⟩

/-! ## The fuel bound and the stage -/

theorem cost_le (X : WriterShape a) (K : KitShape a) (m : LowerMeta a K) (fit : LowerFit X K m) (r : Request) :
    cost K m r ≤ 2 ^ 46 * (K.cC + K.cW + X.cR + m.cM + 1) ^ 26 *
      (r.smallSize a) ^ (26 * (K.dC + K.dW + X.dR + m.dM)) := by
  have hs : 1 ≤ r.smallSize a := RCFive.PacketBounds.positive a r
  have hm := LowerCost.lift_le _ _ _ (K.cC + K.cW + X.cR + m.cM) (K.dC + K.dW + X.dR + m.dM) _ hs
    (by omega) (by omega) (m.cost_le r)
  have hC := LowerCost.lift_le _ _ _ (K.cC + K.cW + X.cR + m.cM) (K.dC + K.dW + X.dR + m.dM) _ hs
    (by omega) (by omega) (K.C_le r)
  have hw := LowerCost.lift_le _ _ _ (K.cC + K.cW + X.cR + m.cM) (K.dC + K.dW + X.dR + m.dM) _ hs
    (by omega) (by omega) (K.w_le r)
  have hX := LowerCost.lift_le _ _ _ (K.cC + K.cW + X.cR + m.cM) (K.dC + K.dW + X.dR + m.dM) _ hs
    (by omega) (by omega) (X.hR r)
  have ht := LowerCost.total_le (m.cost r) (K.C r) (K.w r) (m.cap r) (pool a r).length _ hm hC hw
    ((fit.log r).trans hX) ((fit.reserve r).trans hX)
  exact ht.trans (LowerCost.poly_le _ _ _ _ hs le_rfl)

/-- **F2 at the kit seam**, from the metadata and the room. -/
def stage (X : WriterShape a) (K : KitShape a) (m : LowerMeta a K) (fit : LowerFit X K m) : LowerStageK X K where
  states := _
  machine := machine X m fit.width
  cost := cost K m
  coefficient := 2 ^ 46 * (K.cC + K.cW + X.cR + m.cM + 1) ^ 26
  degree := 26 * (K.dC + K.dW + X.dR + m.dM)
  cost_le := cost_le X K m fit
  run := fun r k hk H A h0A h0H h14A h14H hblank => run X K m fit r k hk H A h0A h0H h14A h14H hblank

end
end NearCubicWires.PacketsConstruction.LowerKit
