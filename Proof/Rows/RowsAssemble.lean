import Proof.Rows.RowsCore

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowReady
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-- **The remaining rows work for one `(a, printer)`**: `coreOf`'s inputs, as one structure of typed holes. -/
structure Parts (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) where
  work : Nat
  drv : Fin (rowWork work)
  lg : Fin (rowWork work)
  reserve : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 440 → Nat
  base : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps →
    Nat → Fin (rowWork work) → List Bool
  completeFuel : Request → RowCaps → Nat
  rowFuel : Request → RowCaps → Nat
  hne : drv ≠ lg
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  completeStates : Nat
  complete : Machine (rowTapes printer work) completeStates
  initializeStates : Nat
  initializer : Machine (rowTapes printer work+1) initializeStates
  initial : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      let entry := PCJ38fbfed565f64139_Family.entry printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_Plan.program (clearSlots printer work drv lg) complete)) (r.family a)
        (stateOf selector a printer work drv lg reserve base completeFuel rowFuel r layout facts caps)
      Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree layout.C caps)
        (fun _ => 0) (rowPublicInput selector a printer work r layout caps)
        entry.heads entry.tapes
  hstep : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      ∀ (j : Fin (r.family a).rows.attach.length) (out : List Bool),
      Step complete (completeFuel r caps)
        (PCJ38fbfed565f64139_Row.headerOutH printer
          (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
            (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out)
          (PCJ38fbfed565f64139_Family.rawBefore a (r.family a) (geometryOf selector a r) j.val)
          (PCJ38fbfed565f64139_Family.rawAfter a (r.family a) (geometryOf selector a r) j.val))
        (PCJ38fbfed565f64139_Row.headerOutA printer
          (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
            (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out)
          (PCJ38fbfed565f64139_Family.rawBefore a (r.family a) (geometryOf selector a r) j.val)
          (PCJ38fbfed565f64139_Family.rawAfter a (r.family a) (geometryOf selector a r) j.val))
        (PCJ38fbfed565f64139_Row.frameInH printer
          (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
          (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
            (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out) out)
        (PCJ38fbfed565f64139_Row.frameInA printer
          (PCJ38fbfed565f64139_Ready.code (prog printer work drv lg completeStates complete))
          a (r.family a) (geometryOf selector a r) layout (rw (r.family a) j).val
          (rw (r.family a) j).property (facts (rw (r.family a) j).val (rw (r.family a) j).property)
          (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
            (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out) out)
  hbud : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      ∀ (j : Fin (r.family a).rows.attach.length) (out : List Bool),
      PCJ38fbfed565f64139_Row.budget printer a (r.family a) (geometryOf selector a r) layout
        (rw (r.family a) j).val (rw (r.family a) j).property
        (facts (rw (r.family a) j).val (rw (r.family a) j).property)
        (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
          (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out) ≤ rowFuel r caps
  cost : ∀ r layout (_facts : ∀ row ∈ (r.family a).rows,
        Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) caps,
      RowCaps.Good selector a printer r layout _facts caps →
      rowFuel r caps ≤ rowBudget a coefficient degree r layout.C caps

variable {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}

/-- The Core built from the parts (`coreOf`). -/
def Parts.core (P : Parts selector a printer) : PCJ45bee56da9f34d5a_Plan.Core selector a printer :=
  coreOf selector a printer P.work P.drv P.lg P.reserve P.base P.completeFuel P.rowFuel P.hne P.coefficient P.degree
    P.positive P.completeStates P.complete P.initializeStates P.initializer P.initial P.hstep P.hbud P.cost

theorem rowConstruction_of_parts (selector : CyclicChoice.Laws)
    (h : ∀ (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm), Nonempty (Parts selector a printer)) :
    RowConstruction selector :=
  PCJ45bee56da9f34d5a_Plan.assemble selector (fun a printer => (h a printer).elim (fun P => ⟨P.core⟩))

end
end RowsConstruction
