import Proof.Rows.RowsCostBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.FinalNE
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowReady
open RowsConstruction.BaseLayout RowsConstruction.CompleteBank RowsConstruction.PartsStep
attribute [local irreducible] P1TopDownPaidPayload.tapes
open RowsConstruction.PartsFill RowsConstruction.CostBound
noncomputable section

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)

structure InitHole' (Rp : Request → Nat) where
  NI : Nat
  pubOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 2 → List Bool
  initOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin NI → List Bool
  rcpOf : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 64 → List Bool
  iMode : Fin NI
  ini : Fin 40 → Fin NI
  ix : Fin 4 → Fin NI
  ib : Fin 82 → Fin NI
  iOne : Fin NI
  iniS : Fin 9 → Fin NI
  c5 : ∀ r layout caps, (r.family a).rows ≠ [] → C5Ready a NI (initOf r layout caps) iMode ini ix ib iOne iniS (Rp r) r
  coefficient : Nat
  degree : Nat
  initializeStates : Nat
  initializer : Machine (rowTapes printer (rowsWork NI)+1) initializeStates
  initial : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      let entry := PCJ38fbfed565f64139_Family.entry printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_Plan.program (clearSlots printer (rowsWork NI) (rowpPort NI 0) (rowpPort NI 1))
            (completeM printer NI (rowsPorts NI) iMode ini ix ib iOne iniS))) (r.family a)
        (RowsConstruction.stateOf selector a printer (rowsWork NI) (rowpPort NI 0) (rowpPort NI 1) (reserveFn selector a)
          (baseFn selector a NI pubOf initOf rcpOf) (fuelOf a Rp) (rowFuelOf printer a Rp) r layout facts caps)
      Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree layout.C caps)
        (fun _ => 0) (rowPublicInput selector a printer (rowsWork NI) r layout caps)
        entry.heads entry.tapes

variable {selector a printer}

theorem rows_ne {q Lq : Nat} {F : Packets.Family q Lq} (j : Fin F.rows.attach.length) : F.rows ≠ [] := by
  intro h
  have hj := j.isLt
  simp [h] at hj

/-- **`Parts.hstep` at RW's choices, from `InitHole'`** (`C5Ready` is needed only for a nonempty family: `rows_ne`). -/
theorem hstepOf' (Rp : Request → Nat) (hRp : ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : Nat),
    ∀ p, p ≤ KeySucc.cut a r target →
      RowsConstruction.ThrPrime.psCost (KeyTop.wT a r four L target) (KeySucc.cut a r target) p + 1 ≤
        Rp (.thr r four L target)) (I : InitHole' selector a printer Rp) :
    ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      ∀ (j : Fin (r.family a).rows.attach.length) (out : List Bool),
      Step (completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini I.ix I.ib I.iOne
          I.iniS) (fuelOf a Rp r caps)
        (PCJ38fbfed565f64139_Row.headerOutH printer
          (PCJ38fbfed565f64139_Ready.code (prog printer (rowsWork I.NI) (rowpPort I.NI 0)
            (rowpPort I.NI 1) _ (completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini
              I.ix I.ib I.iOne I.iniS)))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (bnk printer (rowsWork I.NI) a (r.family a) (geometryOf selector a r) layout facts caps (reserveOf caps)
            (baseFn selector a I.NI I.pubOf I.initOf I.rcpOf r layout caps)
            (rowpPort I.NI 0) (rowpPort I.NI 1) (fuelOf a Rp r caps) (rowFuelOf printer a Rp r caps)
            j out)
          (PCJ38fbfed565f64139_Family.rawBefore a (r.family a) (geometryOf selector a r) j.val)
          (PCJ38fbfed565f64139_Family.rawAfter a (r.family a) (geometryOf selector a r) j.val))
        (PCJ38fbfed565f64139_Row.headerOutA printer
          (PCJ38fbfed565f64139_Ready.code (prog printer (rowsWork I.NI) (rowpPort I.NI 0)
            (rowpPort I.NI 1) _ (completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini
              I.ix I.ib I.iOne I.iniS)))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (bnk printer (rowsWork I.NI) a (r.family a) (geometryOf selector a r) layout facts caps (reserveOf caps)
            (baseFn selector a I.NI I.pubOf I.initOf I.rcpOf r layout caps)
            (rowpPort I.NI 0) (rowpPort I.NI 1) (fuelOf a Rp r caps) (rowFuelOf printer a Rp r caps)
            j out)
          (PCJ38fbfed565f64139_Family.rawBefore a (r.family a) (geometryOf selector a r) j.val)
          (PCJ38fbfed565f64139_Family.rawAfter a (r.family a) (geometryOf selector a r) j.val))
        (PCJ38fbfed565f64139_Row.frameInH printer
          (PCJ38fbfed565f64139_Ready.code (prog printer (rowsWork I.NI) (rowpPort I.NI 0)
            (rowpPort I.NI 1) _ (completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini
              I.ix I.ib I.iOne I.iniS)))
          (bnk printer (rowsWork I.NI) a (r.family a) (geometryOf selector a r) layout facts caps (reserveOf caps)
            (baseFn selector a I.NI I.pubOf I.initOf I.rcpOf r layout caps)
            (rowpPort I.NI 0) (rowpPort I.NI 1) (fuelOf a Rp r caps) (rowFuelOf printer a Rp r caps)
            j out) out)
        (PCJ38fbfed565f64139_Row.frameInA printer
          (PCJ38fbfed565f64139_Ready.code (prog printer (rowsWork I.NI) (rowpPort I.NI 0)
            (rowpPort I.NI 1) _ (completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini
              I.ix I.ib I.iOne I.iniS)))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (rw (r.family a) j).property (facts (rw (r.family a) j).val (rw (r.family a) j).property)
          (bnk printer (rowsWork I.NI) a (r.family a) (geometryOf selector a r) layout facts caps (reserveOf caps)
            (baseFn selector a I.NI I.pubOf I.initOf I.rcpOf r layout caps)
            (rowpPort I.NI 0) (rowpPort I.NI 1) (fuelOf a Rp r caps) (rowFuelOf printer a Rp r caps)
            j out) out) := by
  intro r
  cases r with
  | terminal =>
    intro layout facts caps _ j _
    exact absurd j.isLt (Nat.not_lt_zero _)
  | sym r four L target =>
    intro layout facts caps good j out
    exact hstep_form printer I.NI a _ _ layout facts caps _ _ _ _ _ _ _ j out (copyCap_pos good j)
      (sym_core printer I.NI a (I.pubOf _ layout caps) (I.initOf _ layout caps)
        (I.rcpOf _ layout caps) caps I.iMode I.ini I.ix I.ib I.iOne I.iniS
        r four L target _ layout facts good.2.1 good.1 (I.c5 _ layout caps (rows_ne j)) j out)
  | thr r four L target =>
    intro layout facts caps good j out
    exact hstep_form printer I.NI a _ _ layout facts caps _ _ _ _ _ _ _ j out (copyCap_pos good j)
      (thr_core printer I.NI a (I.pubOf _ layout caps) (I.initOf _ layout caps)
        (I.rcpOf _ layout caps) caps I.iMode I.ini I.ix I.ib I.iOne I.iniS
        r four L target _ layout facts good.2.1 good.1 (Rp _) (I.c5 _ layout caps (rows_ne j)) (hRp r four L target)
        j out)

def partsOf' (I : InitHole' selector a printer (PrimeReserve.rpOf a)) : Parts selector a printer where
  work := rowsWork I.NI
  drv := rowpPort I.NI 0
  lg := rowpPort I.NI 1
  reserve := reserveFn selector a
  base := baseFn selector a I.NI I.pubOf I.initOf I.rcpOf
  completeFuel := fuelOf a (PrimeReserve.rpOf a)
  rowFuel := rowFuelOf printer a (PrimeReserve.rpOf a)
  hne := by
    intro h
    have := congrArg Fin.val h
    rw [rowpPort_val, rowpPort_val] at this
    omega
  coefficient := max (coefficientOf printer) I.coefficient
  degree := max D I.degree
  positive := lt_of_lt_of_le (coefficientOf_pos printer) (le_max_left _ _)
  completeStates := _
  complete := completeM printer I.NI (rowsPorts I.NI) I.iMode I.ini I.ix I.ib I.iOne I.iniS
  initializeStates := I.initializeStates
  initializer := I.initializer
  initial := fun r layout facts caps good =>
    (I.initial r layout facts caps good).enlarge
      (rowInitBudget_mono a r layout.w layout.degree layout.C caps _ _ _ _ (le_max_right _ _) (le_max_right _ _))
  hstep := hstepOf' (PrimeReserve.rpOf a) (PrimeReserve.hRp a) I
  hbud := hbudOf I.NI (PrimeReserve.rpOf a) (baseFn selector a I.NI I.pubOf I.initOf I.rcpOf)
  cost := fun r layout _ caps _ =>
    (cost_le selector a printer r layout.C caps).trans
      (rowBudget_mono a r layout.C caps _ _ _ _ (le_max_left _ _) (le_max_left _ _))

theorem rowConstruction_of_init' (selector : CyclicChoice.Laws)
    (h : ∀ (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm),
      Nonempty (InitHole' selector a printer (PrimeReserve.rpOf a))) :
    RowConstruction selector :=
  rowConstruction_of_parts selector (fun a printer => (h a printer).elim (fun I => ⟨partsOf' I⟩))

end
end RowsConstruction.FinalNE
