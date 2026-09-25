import Proof.Rows.RowsPartsStep
import Proof.Rows.RowsAssemble

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.PartsFill
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowReady
open RowsConstruction.BaseLayout RowsConstruction.CompleteBank RowsConstruction.PartsStep
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. Budget monotonicity (to merge the initializer's and the row's `coefficient/degree`) -/

theorem smallSize_pos (a : DecompositionAlgorithm) (r : Request) : 1 ≤ r.smallSize a := by
  unfold Request.smallSize
  dsimp only
  exact Nat.le_add_left 1 _

theorem rowBudget_mono (a : DecompositionAlgorithm) (r : Request) (C : Nat) (caps : RowCaps) (c c' d d' : Nat)
    (hc : c ≤ c') (hd : d ≤ d') : rowBudget a c d r C caps ≤ rowBudget a c' d' r C caps := by
  unfold rowBudget
  have h1 : (r.smallSize a)^d ≤ (r.smallSize a)^d' := Nat.pow_le_pow_right (smallSize_pos a r) hd
  have h2 : (r.q+(r.input a).length+1)^d ≤ (r.q+(r.input a).length+1)^d' := Nat.pow_le_pow_right (by omega) hd
  have h3 := Nat.mul_le_mul_left (2^(Packets.residual (r.family a))) h2
  exact Nat.mul_le_mul hc (by omega)

theorem rowInitBudget_mono (a : DecompositionAlgorithm) (r : Request) (w D C : Nat) (caps : RowCaps)
    (c c' d d' : Nat) (hc : c ≤ c') (hd : d ≤ d') :
    rowInitBudget a c d r w D C caps ≤ rowInitBudget a c' d' r w D C caps := by
  unfold rowInitBudget
  have h1 := rowBudget_mono a r C caps c c' d d' hc hd
  have h2 := Nat.mul_le_mul_right (caps.rawReserve+caps.descriptorReserve+(r.family a).rows.length+
    (rowMetadataWord w D C caps).length+1) hc
  omega

/-! ## 2. The uniform row fuel and `hbud` -/

/-- A uniform bound of `Row.budget` (`prepareFuel = 0`, `Header.budget ≤ headerFuel`, `completeFuel`,
`Frame.budget ≤ T·(4·copyCap+4)`, `cleanupFuel = 2·copyCap+4`). -/
def rowFuelOf (printer : WilliamsAlgorithm) (a : DecompositionAlgorithm) (Rp : Request → Nat) (r : Request)
    (caps : RowCaps) : Nat :=
  0+1+(caps.headerFuel+1+(fuelOf a Rp r caps+1+
    (P1TopDownPaidPayload.tapes printer*(4*caps.copyCap+4)+1+(2*caps.copyCap+4))))

theorem listCost_le {t : Nat} (fields : Fin t → List Bool) (K : Nat) :
    ∀ js : List (Fin t), (∀ j ∈ js, (fields j).length ≤ K) →
      NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit.listCost fields js ≤ js.length*(4*K+4)
  | [], _ => Nat.zero_le _
  | j :: js, h => by
    have hj := h j (List.mem_cons_self ..)
    have ih := listCost_le fields K js (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit.listCost, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- `Frame.budget ≤ T·(4·copyCap+4)` whenever every field fits the copy capacity (`RowCaps.Good` clause 2). -/
theorem frame_budget_le (printer : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum) (cap : Nat)
    (hfit : ∀ i, 2*(PCJ38fbfed565f64139_Row.Frame.fields printer d i).length+1 ≤ cap) :
    PCJ38fbfed565f64139_Row.Frame.budget printer d ≤ P1TopDownPaidPayload.tapes printer*(4*cap+4) := by
  have h := listCost_le (PCJeb9c0f0306e9481c_FramingSpec.fields (PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d))
    cap (PCJeb9c0f0306e9481c_FramingSpec.fieldSlots (P1TopDownPaidPayload.tapes printer)) (by
      intro j hj
      simp only [PCJeb9c0f0306e9481c_FramingSpec.fieldSlots, List.mem_map] at hj
      obtain ⟨i, _, rfl⟩ := hj
      simp only [PCJeb9c0f0306e9481c_FramingSpec.fields, Fin.addCases_left]
      have := hfit i
      change 2*(PCJeb9c0f0306e9481c_FramingSpec.datumFields printer d i).length+1 ≤ cap at this
      omega)
  simp only [PCJeb9c0f0306e9481c_FramingSpec.fieldSlots, List.length_map, List.length_finRange] at h
  exact h

/-! ## 3. The holes -/

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)

/-- `base` at the initializer's request-constant blocks. -/
abbrev baseFn (NI : Nat)
    (pubOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 2 → List Bool)
    (initOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin NI → List Bool)
    (rcpOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 64 → List Bool)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Nat → Fin (rowWork (rowsWork NI)) → List Bool :=
  baseOf a NI (pubOf r layout caps) (initOf r layout caps) (rcpOf r layout caps) layout.C caps.copyCap
    caps.headerFuel r

abbrev reserveFn : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 440 → Nat :=
  fun _ _ caps => reserveOf caps

/-! ## 4. `Parts` from the holes -/

variable {selector a printer}

theorem copyCap_pos {r : Request} {layout : Packets.Layout a (r.family a) (geometryOf selector a r)}
    {facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row}
    {caps : RowCaps} (good : RowCaps.Good selector a printer r layout facts caps)
    (j : Fin (r.family a).rows.attach.length) : 1 ≤ caps.copyCap := by
  have h := good.2.1 _ (PCJ38fbfed565f64139_Family.rowAt _ j).property (RowsRowLevel.fieldPort printer 0)
  omega

/-- **`Parts.hbud`**: `Row.budget ≤ rowFuelOf` from `RowCaps.Good`. -/
theorem hbudOf (NI : Nat) (Rp : Request → Nat)
    (base : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps →
      Nat → Fin (rowWork (rowsWork NI)) → List Bool) :
    ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      ∀ (j : Fin (r.family a).rows.attach.length) (out : List Bool),
      PCJ38fbfed565f64139_Row.budget printer a (r.family a) (geometryOf selector a r) layout
        (rw (r.family a) j).val (rw (r.family a) j).property
        (facts (rw (r.family a) j).val (rw (r.family a) j).property)
        (bnk printer (rowsWork NI) a (r.family a) (geometryOf selector a r) layout facts caps (reserveOf caps)
          (base r layout caps) (rowpPort NI 0) (rowpPort NI 1) (fuelOf a Rp r caps) (rowFuelOf printer a Rp r caps)
          j out) ≤ rowFuelOf printer a Rp r caps := by
  intro r layout facts caps good j out
  have hH := good.1 _ (rw (r.family a) j).property
  have hF := frame_budget_le printer
    (Packets.datum a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val (rw (r.family a) j).property
      (facts (rw (r.family a) j).val (rw (r.family a) j).property)) caps.copyCap
    (good.2.1 _ (rw (r.family a) j).property)
  change 0+1+(PCJcc051fd4c1bd4540_Header.budget a (r.family a) (geometryOf selector a r) layout
      (rw (r.family a) j).val+1+(fuelOf a Rp r caps+1+
      (PCJ38fbfed565f64139_Row.Frame.budget printer
        (Packets.datum a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (rw (r.family a) j).property (facts (rw (r.family a) j).val (rw (r.family a) j).property))+1+
        (2*caps.copyCap+4)))) ≤ _
  unfold rowFuelOf
  omega

end
end RowsConstruction.PartsFill
