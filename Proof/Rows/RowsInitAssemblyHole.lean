import Proof.Rows.RowsInitAssemblyRun
import Proof.Rows.RowsInitCostTotal
import Proof.Rows.RowsFrameEntry
import Proof.Rows.RowsHeaderWFinal

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.InitAssembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketFamilyParent
open RowsInit.Global
noncomputable section

section Hole
variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)

/-- RH's closed Header writer. -/
abbrev hW : RowsInit.Hdr.HdrSpec selector a printer := RowsHeaderW.hdrSpec selector a printer

/-- The initializer's index count at RH's writer. -/
abbrev nIH : ℕ := NI a (hW selector a printer).needH

open Classical in
/-- The public block, read off the initializer's own final bank. -/
def holePub (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Fin 2 → List Bool :=
  if h : ∃ F, Final selector a printer (hW selector a printer) r layout caps F then
    fun i => Classical.choose h (wS printer (nIH selector a printer) (pubPort (nIH selector a printer) i))
  else fun _ => []

open Classical in
/-- The init block, read off the initializer's own final bank (off `Good`: the work phase's `C5Ready` block). -/
def holeInit (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Fin (nIH selector a printer) → List Bool :=
  if h : ∃ F, Final selector a printer (hW selector a printer) r layout caps F then
    fun i => Classical.choose h (wS printer (nIH selector a printer) (initPort (nIH selector a printer) i))
  else Classical.choose (c5_wit selector a printer (hW selector a printer) r)

open Classical in
/-- The rcp block, read off the initializer's own final bank. -/
def holeRcp (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Fin 64 → List Bool :=
  if h : ∃ F, Final selector a printer (hW selector a printer) r layout caps F then
    fun i => Classical.choose h (wS printer (nIH selector a printer) (rcpPort (nIH selector a printer) i))
  else fun _ => []

theorem hole_c5 (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps)
    (hne : (r.family a).rows ≠ []) :
    PartsStep.C5Ready a (nIH selector a printer) (holeInit selector a printer r layout caps)
      (RowsInit.ThrInitReady.iMode (nIH selector a printer) (h146 a (hW selector a printer).needH))
      (RowsInit.ThrInitReady.ini (nIH selector a printer) (h146 a (hW selector a printer).needH))
      (RowsInit.ThrInitReady.ix (nIH selector a printer) (h146 a (hW selector a printer).needH))
      (RowsInit.ThrInitReady.ib (nIH selector a printer) (h146 a (hW selector a printer).needH))
      (RowsInit.ThrInitReady.iOne (nIH selector a printer) (h146 a (hW selector a printer).needH))
      (RowsInit.ThrInitReady.iniS (nIH selector a printer) (h146 a (hW selector a printer).needH)) (PrimeReserve.rpOf a r) r := by
  by_cases h : ∃ F, Final selector a printer (hW selector a printer) r layout caps F
  · have e : holeInit selector a printer r layout caps =
        fun i => Classical.choose h (wS printer (nIH selector a printer) (initPort (nIH selector a printer) i)) := by
      unfold holeInit
      rw [dif_pos h]
    rw [e]
    exact (Classical.choose_spec h).2.2.2.2.2 hne
  · have e : holeInit selector a printer r layout caps = Classical.choose (c5_wit selector a printer (hW selector a printer) r) := by
      unfold holeInit
      rw [dif_neg h]
    rw [e]
    exact Classical.choose_spec (c5_wit selector a printer (hW selector a printer) r) hne

/-- The completion code of `InitHole'.initial`'s entry, at the filled index maps. -/
abbrev codeH :=
  PCJ38fbfed565f64139_Ready.code
    (PCJ45bee56da9f34d5a_Plan.program
      (PCJ45bee56da9f34d5a_RowState.clearSlots printer (rowsWork (nIH selector a printer)) (rowpPort (nIH selector a printer) 0)
        (rowpPort (nIH selector a printer) 1))
      (RowsConstruction.CompleteBank.completeM printer (nIH selector a printer) (RowsConstruction.PartsStep.rowsPorts (nIH selector a printer))
        (RowsInit.ThrInitReady.iMode (nIH selector a printer) (h146 a (hW selector a printer).needH))
        (RowsInit.ThrInitReady.ini (nIH selector a printer) (h146 a (hW selector a printer).needH))
        (RowsInit.ThrInitReady.ix (nIH selector a printer) (h146 a (hW selector a printer).needH))
        (RowsInit.ThrInitReady.ib (nIH selector a printer) (h146 a (hW selector a printer).needH))
        (RowsInit.ThrInitReady.iOne (nIH selector a printer) (h146 a (hW selector a printer).needH))
        (RowsInit.ThrInitReady.iniS (nIH selector a printer) (h146 a (hW selector a printer).needH))))

/-- **The initializer's side, filled**: every field of `InitHole'` at RW's machine, RH's Header writer, RF's entry identities and
RS's cost constants. -/
def hole : FinalNE.InitHole' selector a printer (PrimeReserve.rpOf a) where
  NI := nIH selector a printer
  pubOf := holePub selector a printer
  initOf := holeInit selector a printer
  rcpOf := holeRcp selector a printer
  iMode := RowsInit.ThrInitReady.iMode (nIH selector a printer) (h146 a (hW selector a printer).needH)
  ini := RowsInit.ThrInitReady.ini (nIH selector a printer) (h146 a (hW selector a printer).needH)
  ix := RowsInit.ThrInitReady.ix (nIH selector a printer) (h146 a (hW selector a printer).needH)
  ib := RowsInit.ThrInitReady.ib (nIH selector a printer) (h146 a (hW selector a printer).needH)
  iOne := RowsInit.ThrInitReady.iOne (nIH selector a printer) (h146 a (hW selector a printer).needH)
  iniS := RowsInit.ThrInitReady.iniS (nIH selector a printer) (h146 a (hW selector a printer).needH)
  c5 := hole_c5 selector a printer
  coefficient := Classical.choose (RowsInit.CostTotal.init_cost_le selector a printer (hW selector a printer))
  degree := Classical.choose (Classical.choose_spec (RowsInit.CostTotal.init_cost_le selector a printer (hW selector a printer)))
  initializeStates := _
  initializer := initM selector a printer (hW selector a printer)
  initial := by
    intro r layout facts caps good
    have hex := final_run selector a printer (hW selector a printer) r layout facts caps good
    have hF := Classical.choose_spec hex
    have ep : holePub selector a printer r layout caps =
        fun i => Classical.choose hex (wS printer (nIH selector a printer) (pubPort (nIH selector a printer) i)) := by
      unfold holePub
      rw [dif_pos hex]
    have ei : holeInit selector a printer r layout caps =
        fun i => Classical.choose hex (wS printer (nIH selector a printer) (initPort (nIH selector a printer) i)) := by
      unfold holeInit
      rw [dif_pos hex]
    have er : holeRcp selector a printer r layout caps =
        fun i => Classical.choose hex (wS printer (nIH selector a printer) (rcpPort (nIH selector a printer) i)) := by
      unfold holeRcp
      rw [dif_pos hex]
    have hw : ∀ x, Classical.choose hex (wS printer (nIH selector a printer) x) =
        PCJ45bee56da9f34d5a_RowState.workBank (rowsWork (nIH selector a printer)) caps
          (baseOf a (nIH selector a printer) (holePub selector a printer r layout caps) (holeInit selector a printer r layout caps)
            (holeRcp selector a printer r layout caps) layout.C caps.copyCap caps.headerFuel r)
          (rowpPort (nIH selector a printer) 0) (rowpPort (nIH selector a printer) 1) 0 x := by
      rw [ep, ei, er]
      exact hF.2.2.2.2.1
    have hcost := Classical.choose_spec (Classical.choose_spec
      (RowsInit.CostTotal.init_cost_le selector a printer (hW selector a printer))) r layout caps
    have hh := RowsInit.FrameEntry.entry_heads selector a printer (nIH selector a printer) (holePub selector a printer)
      (holeInit selector a printer) (holeRcp selector a printer) (PrimeReserve.rpOf a)
      (codeH selector a printer)
      r layout facts caps
    have ht := RowsInit.FrameEntry.entry_tapes selector a printer (nIH selector a printer) (holePub selector a printer)
      (holeInit selector a printer) (holeRcp selector a printer) (PrimeReserve.rpOf a)
      (codeH selector a printer)
      r layout facts caps (Classical.choose hex) hF.2.1 hF.2.2.2.1 hw hF.2.2.1
    show Step _ _ _ _ (RowsInit.FrameEntry.E selector a printer (nIH selector a printer) (holePub selector a printer)
      (holeInit selector a printer) (holeRcp selector a printer) (PrimeReserve.rpOf a) (codeH selector a printer) r layout facts caps).heads
      (RowsInit.FrameEntry.E selector a printer (nIH selector a printer) (holePub selector a printer)
      (holeInit selector a printer) (holeRcp selector a printer) (PrimeReserve.rpOf a) (codeH selector a printer) r layout facts caps).tapes
    rw [hh, ht]
    exact hF.1.enlarge hcost

end Hole

theorem rowConstruction_final (selector : CyclicChoice.Laws) : RowConstruction selector :=
  FinalNE.rowConstruction_of_init' selector (fun a printer => ⟨hole selector a printer⟩)

end
end RowsConstruction.InitAssembly
