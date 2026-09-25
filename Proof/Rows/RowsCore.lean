import Proof.Rows.RowReady

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

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (work : Nat) (drv lg : Fin (rowWork work))
  (reserve : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → Fin 440 → Nat)
  (base : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps →
    Nat → Fin (rowWork work) → List Bool)
  (completeFuel rowFuel : Request → RowCaps → Nat)

def stateOf (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (_facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps) :
    PCJ38fbfed565f64139_Family.State (t:=rowTapes printer work) printer :=
  rowState printer work a (r.family a) (geometryOf selector a r) layout caps (reserve r layout caps) (base r layout caps)
    drv lg (completeFuel r caps) (rowFuel r caps)

/-- **The rows parent.** Every Core field except the open ones, for an arbitrary `complete`. -/
def coreOf (hne : drv ≠ lg) (coefficient degree : Nat) (positive : 0 < coefficient)
    (completeStates : Nat) (complete : Machine (rowTapes printer work) completeStates)
    (initializeStates : Nat) (initializer : Machine (rowTapes printer work+1) initializeStates)
    (initial : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      let entry := PCJ38fbfed565f64139_Family.entry printer
        (PCJ38fbfed565f64139_Ready.code
          (PCJ45bee56da9f34d5a_Plan.program (clearSlots printer work drv lg) complete)) (r.family a)
        (stateOf selector a printer work drv lg reserve base completeFuel rowFuel r layout facts caps)
      Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree layout.C caps)
        (fun _ => 0) (rowPublicInput selector a printer work r layout caps)
        entry.heads entry.tapes)
    (hstep : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
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
            (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out) out))
    (hbud : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
      ∀ (j : Fin (r.family a).rows.attach.length) (out : List Bool),
      PCJ38fbfed565f64139_Row.budget printer a (r.family a) (geometryOf selector a r) layout
        (rw (r.family a) j).val (rw (r.family a) j).property
        (facts (rw (r.family a) j).val (rw (r.family a) j).property)
        (bnk printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
          (base r layout caps) drv lg (completeFuel r caps) (rowFuel r caps) j out) ≤ rowFuel r caps)
    (cost : ∀ r layout (_facts : ∀ row ∈ (r.family a).rows,
        Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) caps,
      RowCaps.Good selector a printer r layout _facts caps →
      rowFuel r caps ≤ rowBudget a coefficient degree r layout.C caps) :
    PCJ45bee56da9f34d5a_Plan.Core selector a printer where
  privateWork := work
  coefficient := coefficient
  degree := degree
  positive := positive
  mutableTapes := P1TopDownPaidPayload.tapes printer
  slots := clearSlots printer work drv lg
  injective := clear_injective printer work drv lg hne
  completeStates := completeStates
  complete := complete
  initializeStates := initializeStates
  initializer := initializer
  state := stateOf selector a printer work drv lg reserve base completeFuel rowFuel
  initial := initial
  completeReady := fun r layout facts caps good j out =>
    ready_body printer work a (r.family a) (geometryOf selector a r) layout facts caps (reserve r layout caps)
      (base r layout caps) drv lg completeStates complete (completeFuel r caps) (rowFuel r caps) j out hne
      (good.2.1 (rw (r.family a) j).val (rw (r.family a) j).property)
      (hstep r layout facts caps good j out) (hbud r layout facts caps good j out)
  descriptor := fun r layout _ caps _ j _ out =>
    ⟨descriptor_heads printer work a (r.family a) (geometryOf selector a r) j out,
      descriptor_tapes printer work a (r.family a) (geometryOf selector a r) layout caps
        (reserve r layout caps) (base r layout caps) drv lg j out⟩
  cost := cost

end
end RowsConstruction
