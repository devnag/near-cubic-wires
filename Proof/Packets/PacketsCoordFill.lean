import Proof.Packets.PacketsCoordDonorLoop

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.Donor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsGlue.RequestMeta
open Theorem25Completion.CycleBounds
noncomputable section

variable {a : DecompositionAlgorithm}

theorem tapesEqD (D : ℕ) : UnaryCalc.tapes D = 2 + (12 + 2 * D) := by
  simp only [UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

def castD (D : ℕ) : Fin (UnaryCalc.tapes D) → Fin (2 + (12 + 2 * D)) := Fin.cast (tapesEqD D)

theorem castD_inj (D : ℕ) : Function.Injective (castD D) := Fin.cast_injective _

theorem castD_val (D : ℕ) (j : Fin (UnaryCalc.tapes D)) : (castD D j).val = j.val := rfl

theorem castD_out_ne (D : ℕ) : (castD D (UnaryCalc.outputTape D)).val ≠ 0 := by
  intro h
  rw [castD_val] at h
  exact UnaryCalc.output_ne_input D (Fin.ext (by rw [h]; rfl))

/-- **`x ↦ C·(x+1)^D`** in unary. -/
def polyMapD (D C : ℕ) : UnaryMap (fun x => UnaryCalc.value D C x) :=
  UnaryMap.ofSwap (e := 12 + 2 * D) (RecoveryFocus.machine (castD D) (PCPSerializerCapacity.Power.machine D C))
    (castD D (UnaryCalc.outputTape D)) (castD_out_ne D) (PCPSerializerCapacity.Power.budget D C) (fun x => by
      obtain ⟨out, h, _, h1⟩ := UnaryCalc.poly_step D C x
      have d := h.dock (castD D) (castD_inj D) (fun _ => 0) (unIn (2 + (12 + 2 * D)) x) (fun _ => rfl) (by
        intro j
        simp only [unIn, RepairSource.ProjectionNormalization.DimensionPolynomial.input, castD_val]
        by_cases hj : j.val = 0 <;> simp [hj])
      refine ⟨_, d.congr (ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl, ?_⟩
      rw [install_slot _ (castD_inj D)]
      exact h1)

theorem polyD_cost (D C x : ℕ) : (polyMapD D C).cost x ≤ UnaryCalc.polyCoefficient D C * (x + 3) ^ (D + 1) := by
  have h := UnaryCalc.poly_cost_polyBounded D C x
  unfold ValidatorPolynomialDomination.PolyBounded at h
  have hm : (x + 1) ^ (D + 1) ≤ (x + 3) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
  exact le_trans h (Nat.mul_le_mul_left _ hm)

/-! ## The constants -/

section Consts
variable {K : KitShape a} (C : CellParts a K)

/-- The uniform cell fuel (`midCost` with the external budget replaced by its every-request bound). -/
def mbv (r : Request) : ℕ :=
  C.mid.prepCost r + 1 + (2 ^ 119 * commonReserve (K.C r) (K.w r) ^ 27 + C.mid.termS.cost r + 2)

/-- The vector length (`vec_length`). -/
def Lv (K : KitShape a) (r : Request) : ℕ :=
  ((r.family a).occurrences.length + 1) * (2 * commonReserve (K.C r) (K.w r))

/-- Everything the loop's driver must dominate. -/
def need (r : Request) : ℕ :=
  mbv C r + Lv K r + (CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) + 1)

theorem hmb (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r) (j : ℕ) :
    C.mid.midCost r k j ≤ mbv C r := by
  have := budgetOf_le a K hA r k j
  unfold MidParts.midCost mbv
  omega

theorem small_pb : PB a (fun r => r.smallSize a) := PB.of_le 1 1 (fun r => by simp)

theorem prep_pb : PB a C.mid.prepCost := by
  have k1 := PB.of_le _ _ C.mid.bS.cost_le
  have k2 := PB.of_le _ _ C.mid.popS.cost_le
  have k3 := PB.of_le _ _ C.mid.cS.cost_le
  have k4 := PB.of_le _ _ C.mid.rootS.cost_le
  have k5 := PB.of_le _ _ C.mid.maskS.cost_le
  have k6 := PB.of_le _ _ C.mid.labelsS.cost_le
  have k7 := PB.of_le _ _ C.mid.nS.cost_le
  have k8 := PB.of_le _ _ C.mid.xS.cost_le
  have k9 := PB.of_le _ _ C.mid.yS.cost_le
  have k10 := PB.of_le _ _ C.mid.wS.cost_le
  have s1 := PB.add (PB.add (PB.add (PB.add k1 k2 (fun _ => le_refl _)) k3 (fun _ => le_refl _)) k4
    (fun _ => le_refl _)) k5 (fun _ => le_refl _)
  have s2 := PB.add (PB.add (PB.add (PB.add k6 k7 (fun _ => le_refl _)) k8 (fun _ => le_refl _)) k9
    (fun _ => le_refl _)) k10 (fun _ => le_refl _)
  refine PB.add (PB.add s1 s2 (fun _ => le_refl _)) (PB.const 9) (fun r => ?_)
  unfold MidParts.prepCost
  omega

theorem mbv_pb : PB a (mbv C) := by
  have hr := PB.mul (PB.const (2 ^ 119)) (PB.pow (reserve_pb K) 27 (fun _ => le_refl _)) (fun _ => le_refl _)
  have ht := PB.of_le _ _ C.mid.termS.cost_le
  refine PB.add (PB.add (prep_pb C) (PB.add hr ht (fun _ => le_refl _)) (fun _ => le_refl _)) (PB.const 3)
    (fun r => ?_)
  unfold mbv
  omega

theorem Lv_pb (K : KitShape a) : PB a (Lv K) :=
  PB.mul (PB.add (pop_pb K) (PB.const 1) (fun _ => le_refl _))
    (PB.mul (PB.const 2) (reserve_pb K) (fun _ => le_refl _)) (fun _ => le_refl _)

theorem app_pb : PB a (fun r => C.app.cost (Lv K r)) :=
  PB.mul (PB.const C.app.costC) (PB.pow (PB.add (Lv_pb K) (PB.const 1) (fun _ => le_refl _)) C.app.costD
    (fun _ => le_refl _)) (fun r => C.app.cost_le (Lv K r))

theorem cell_pb : PB a (fun r => CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4)) := by
  refine PB.add (PB.add (PB.mul (PB.const 2) (mbv_pb C) (fun _ => le_refl _)) (app_pb C) (fun _ => le_refl _))
    (PB.add small_pb (PB.const 9) (fun _ => le_refl _)) (fun r => ?_)
  unfold CellParts.cellCost
  omega

theorem need_pb : PB a (need C) := by
  refine PB.add (PB.add (mbv_pb C) (Lv_pb K) (fun _ => le_refl _))
    (PB.add (cell_pb C) (PB.const 1) (fun _ => le_refl _)) (fun r => ?_)
  unfold need
  omega

/-- The loop's cap (`hcap` at `maskCount ≤ smallSize + 4`). -/
def capv (R : Request → ℕ) (r : Request) : ℕ :=
  (r.smallSize a + 4) * (2 * CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) + 2 + 1 +
    (2 * R r + 4) + 3) + 3

theorem capv_pb (R : Request → ℕ) (hR : PB a R) : PB a (capv C R) := by
  have hin : PB a (fun r => 2 * CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) + 2 + 1 +
      (2 * R r + 4) + 3) :=
    PB.add (PB.mul (PB.const 2) (cell_pb C) (fun _ => le_refl _))
      (PB.add (PB.mul (PB.const 2) hR (fun _ => le_refl _)) (PB.const 10) (fun _ => le_refl _)) (fun r => by omega)
  exact PB.add (PB.mul (PB.add small_pb (PB.const 4) (fun _ => le_refl _)) hin (fun _ => le_refl _)) (PB.const 3)
    (fun _ => le_refl _)

theorem hcap_le (R : Request → ℕ) (r : Request) (k : rcKey a r) :
    maskCount a r k * (2 * CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (maskCount a r k) + 2 + 1 +
      (2 * R r + 4) + 3) + 3 ≤ capv C R r := by
  have hm := maskCount_le (a := a) r k
  have hc : CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (maskCount a r k) ≤
      CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) := by
    unfold CellParts.cellCost; omega
  unfold capv
  have := Nat.mul_le_mul hm (show 2 * CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (maskCount a r k) + 2 + 1 +
      (2 * R r + 4) + 3 ≤ 2 * CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) + 2 + 1 +
      (2 * R r + 4) + 3 by omega)
  omega

end Consts

/-! ## The exact run, padded -/

/-- The pad caps: `0` on the input and key tapes, `Q` on the rest. -/
def padCap (Q t : ℕ) (i : Fin t) : ℕ := if i.val < 9 then 0 else Q

theorem entry_pad {K : KitShape a} (D : Parts a K) (r : Request) (k : rcKey a r) (Llog cap Q : ℕ)
    (hL : Llog ≤ Q) (hc : cap ≤ Q) (hR : D.Rv r ≤ Q) :
    (fun i => ZeroPadding.pad (padCap Q D.T i)
      (dEntry a r k D.T D.S (modeBit r) (D.Lv r) (D.Rv r) Llog cap (maskCount a r k) i)) =
      donorEntry a r k Q D.T := by
  funext i
  unfold padCap donorEntry dEntry
  by_cases h9 : i.val < 9
  · rw [if_pos h9, if_pos h9, if_pos h9, ZeroPadding.pad_zero]
  · rw [if_neg h9, if_neg h9, if_neg h9]
    by_cases h17 : i.val < 17
    · rw [if_pos h17]
      unfold portWord
      simp only [Bool.false_eq_true, if_false]
      split_ifs
      · exact Dock.pad_nil_eq Q
      · exact Dock.pad_nil_eq Q
      · rw [Dock.pad_zeros _ _ hL, Dock.pad_nil_eq]
      · exact Dock.pad_nil_eq Q
      · exact Dock.pad_nil_eq Q
      · rw [Dock.pad_zeros _ _ hc, Dock.pad_nil_eq]
      · exact Dock.pad_nil_eq Q
    · rw [if_neg h17]
      split_ifs
      · rw [Dock.pad_zeros _ _ hR, Dock.pad_nil_eq]
      · exact Dock.pad_nil_eq Q

theorem donor_run {K : KitShape a} (D : Parts a K) (hA : ConeBounds.RouteA a K) (r : Request) (k : rcKey a r)
    (hk : k ∈ rcKeys a r) (mb cap Q : ℕ)
    (hmb : ∀ j, j < maskCount a r k → D.cell.mid.midCost r k j ≤ mb) (hmbR : mb ≤ D.Rv r)
    (hlen : ∀ j, j < maskCount a r k → (vecOf a K r k j).length = D.Lv r) (hLR : D.Lv r ≤ D.Rv r)
    (hR : CellParts.cellCost mb (D.cell.app.cost (D.Lv r)) (maskCount a r k) + 1 ≤ D.Rv r)
    (hcap : maskCount a r k * (2 * CellParts.cellCost mb (D.cell.app.cost (D.Lv r)) (maskCount a r k) + 2 + 1 +
      (2 * D.Rv r + 4) + 3) + 3 ≤ cap)
    (hQ : D.Rv r + 1 + cap ≤ Q) :
    ∃ (H : Fin D.T → ℕ) (A : Fin D.T → List Bool),
      Step (Composition.machine D.preMachine D.mainMachine) (D.preCost r + 1 + (2 * cap + 2)) (fun _ => 0)
        (donorEntry a r k Q D.T) H A ∧
      (∀ i : Fin D.T, i.val < 9 → A i = PacketsCombine.metaEntry a r (some k) D.T i ∧ H i = 0) ∧
      A ⟨9, by have := D.T_ge; omega⟩ = ZeroPadding.pad Q (coordWordK K r k) ∧ H ⟨9, by have := D.T_ge; omega⟩ = 0 ∧
      A ⟨10, by have := D.T_ge; omega⟩ = ZeroPadding.pad Q [modeBit r] ∧ H ⟨10, by have := D.T_ge; omega⟩ = 0 := by
  refine (pre_run D r k hk (D.Rv r + 1) cap).elim fun H1 e1 => e1.elim fun A1 f1 => ?_
  have s1 := f1.1
  refine (main_run D hA r k hk (D.Rv r + 1) mb cap hmb hmbR hlen hLR hR (le_refl _) hcap H1 A1 f1.2).elim
    fun H2 e2 => e2.elim fun A2 f2 => ?_
  have s2 := f2.1
  have hx := f2.2
  have sp := step_pad (Step.seq s1 s2) (padCap Q D.T)
  have sp' := sp.congr_in rfl (entry_pad D r k (D.Rv r + 1) cap Q (by omega) (by omega) (by omega))
  refine ⟨H2, fun i => ZeroPadding.pad (padCap Q D.T i) (A2 i), sp', ?_, ?_, hx.2.2.1, ?_, hx.2.2.2.2⟩
  · intro i hi
    have e := hx.1 i hi
    refine ⟨?_, e.2⟩
    change ZeroPadding.pad (padCap Q D.T i) (A2 i) = _
    rw [e.1]
    unfold padCap
    rw [if_pos hi, ZeroPadding.pad_zero]
  · change ZeroPadding.pad (padCap Q D.T ⟨9, _⟩) (A2 ⟨9, _⟩) = _
    rw [hx.2.1]
    rfl
  · change ZeroPadding.pad (padCap Q D.T ⟨10, _⟩) (A2 ⟨10, _⟩) = _
    rw [hx.2.2.2.1]
    rfl

theorem donor_nonempty {K : KitShape a} (hA : ConeBounds.RouteA a K) (C : CellParts a K)
    (lS : KeyWord a (fun r _ => List.replicate (((r.family a).occurrences.length + 1) *
      (2 * commonReserve (K.C r) (K.w r))) true))
    (mS : KeyWord a (fun r _ => [modeBit r]))
    (cS : KeyWord a (fun r k => CompareMachine.word (maskCount a r k)))
    {base : Request → ℕ} (baseS : UnaryStage a base) (hsb : ∀ r, r.smallSize a ≤ base r) (hbp : PB a base) :
    Nonempty (CoordDonor a K) := by
  obtain ⟨cN, dN, hN⟩ := need_pb C
  let Rv : Request → ℕ := fun r => UnaryCalc.value dN cN (base r)
  have hRv : ∀ r, need C r ≤ Rv r := fun r =>
    lift_base _ cN dN cN dN _ _ (hN r) (hsb r) (le_refl _) (le_refl _)
  have hRpb : PB a Rv :=
    PB.mul (PB.const cN) (PB.pow (PB.add hbp (PB.const 1) (fun _ => le_refl _)) dN (fun _ => le_refl _))
      (fun r => le_refl _)
  let rS : KeyWord a (fun r _ => List.replicate (Rv r) true) :=
    KeyWord.ofWord (baseS.thenMapP (polyMapD dN cN) (UnaryCalc.polyCoefficient dN cN) (dN + 1)
      (polyD_cost dN cN)).toWord
  let D : Parts a K := ⟨C, Rv, Lv K, rS, lS, mS, cS⟩
  let padW : Request → ℕ := fun r => Rv r + 1 + capv C Rv r
  have hpad : PB a padW :=
    PB.add (PB.add hRpb (PB.const 1) (fun _ => le_refl _)) (capv_pb C Rv hRpb) (fun _ => le_refl _)
  let cost : Request → ℕ := fun r => D.preCost r + 1 + (2 * capv C Rv r + 2)
  have hpre : PB a D.preCost := by
    refine PB.add (PB.add (PB.add (PB.of_le _ _ rS.cost_le) (PB.of_le _ _ lS.cost_le) (fun _ => le_refl _))
      (PB.add (PB.of_le _ _ mS.cost_le) (PB.of_le _ _ cS.cost_le) (fun _ => le_refl _)) (fun _ => le_refl _))
      (PB.const 5) (fun r => ?_)
    change rS.cost r + 1 + lS.cost r + 1 + mS.cost r + 1 + cS.cost r + 1 + 1 ≤ _
    omega
  obtain ⟨cc, dc, hc⟩ : PB a cost := PB.add (PB.add hpre (PB.const 3) (fun _ => le_refl _))
    (PB.mul (PB.const 2) (capv_pb C Rv hRpb) (fun _ => le_refl _))
    (fun r => by change D.preCost r + 1 + (2 * capv C Rv r + 2) ≤ _; omega)
  exact ⟨{
    extra := D.extra
    states := _
    machine := Composition.machine D.preMachine D.mainMachine
    cost := cost
    costC := cc
    costD := dc
    cost_le := hc
    padW := padW
    padW_pb := hpad
    run := fun r k hk => by
      have hn := hRv r
      have hm := maskCount_le (a := a) r k
      unfold need at hn
      exact donor_run D hA r k hk (mbv C r) (capv C Rv r) (padW r) (fun j _ => hmb C hA r k j)
        (by change mbv C r ≤ Rv r; omega)
        (fun j hj => vec_length a K hA r k hk j hj) (by change Lv K r ≤ Rv r; omega)
        (by
          change CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (maskCount a r k) + 1 ≤ Rv r
          have : CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (maskCount a r k) ≤
              CellParts.cellCost (mbv C r) (C.app.cost (Lv K r)) (r.smallSize a + 4) := by
            unfold CellParts.cellCost; omega
          omega)
        (hcap_le C Rv r k) (le_refl _) }⟩

theorem coordFam_nonempty {K : KitShape a} (hA : ConeBounds.RouteA a K) (C : CellParts a K)
    (lS : KeyWord a (fun r _ => List.replicate (((r.family a).occurrences.length + 1) *
      (2 * commonReserve (K.C r) (K.w r))) true))
    (mS : KeyWord a (fun r _ => [modeBit r]))
    (cS : KeyWord a (fun r k => CompareMachine.word (maskCount a r k)))
    {base : Request → ℕ} (baseS : UnaryStage a base) (hsb : ∀ r, r.smallSize a ≤ base r) (hbp : PB a base) :
    Nonempty (CoordFam a K) :=
  (donor_nonempty hA C lS mS cS baseS hsb hbp).map CoordDonor.fam

end
end NearCubicWires.PacketsConstruction.Residual.Donor
