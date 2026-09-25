import Proof.CaseAnalysis.FiveNativeResources
import Proof.SourceAssembly.SourceRowWidth

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal SupplierEstimator SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace NearCubicWires.SourceConstruction.Native
noncomputable section

/-- The uniform constant `U0 = 3(K+1) + 2⌈(q−K)/2⌉ + 6`. -/
abbrev U0Of (q K : Nat) : Nat := 3 * (K + 1) + 2 * ((q - K + 1) / 2) + 6

abbrev M2Of (deg K : Nat) : Nat := 2 * (deg * (K + 1))

/-- `RowWidth.rowWidth_formula` at the EFFECTIVE degree `min layout.degree |pool|` (no `degree ≤ |pool|`). -/
theorem rowWidth_formula_min {q L : ℕ} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g) (r : Packets.Row F.occurrences L)
    (hr : r ∈ F.rows) (facts : Packets.PacketFacts a F g r) (deg : ℕ)
    (hmin : min layout.degree (Packets.pool a F g).length = deg) :
    CompetitorSelectedCount.scalarWidth (EquationRow.request (Packets.datum a F g layout r hr facts).row)
      (Packets.datum a F g layout r hr facts).Q =
    2 * (deg * ((Packets.live F).card + 1)) *
        ((exactListWord (C10SupplierRowInput.childList a (Packets.live F) F.occurrences)).length + 1) +
      (3 * ((Packets.live F).card + 1) + 2 * ((Packets.residual F + 1)/2) + 6) := by
  show (Packets.live F).card + 1 + CompetitorSelectedCount.extraWidth
    (EquationRow.request (Packets.rowInput a F g layout r hr facts)) = _
  rw [CompetitorSelectedCount.extraWidth_eq]
  have hd : (EquationRow.request (Packets.rowInput a F g layout r hr facts)).d =
      (Packets.residual F + 1)/2 := rfl
  have hp : (EquationRow.request (Packets.rowInput a F g layout r hr facts)).p =
      P1Closure.CompactBounds.radix a (Packets.live F) F.occurrences *
        (min layout.degree (Packets.pool a F g).length * ((Packets.live F).card+1)) +
        ((Packets.live F).card+1) + 1 := rfl
  rw [hd, hp, hmin]
  unfold P1Closure.CompactBounds.radix
  ring

theorem native_rows (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (printer : WilliamsAlgorithm)
    (layout : Packets.Layout (decompositionOf sources) (Packets.request sources L target mode atoms)
      (Packets.geometry selector (Packets.request sources L target mode atoms)))
    (V deg : Nat)
    (hdeg : min layout.degree (Packets.pool (decompositionOf sources) (Packets.request sources L target mode atoms)
      (Packets.geometry selector (Packets.request sources L target mode atoms))).length = deg)
    (hC : RCFive.NativeResources.streamCap (decompositionOf sources)
      (Packets.request sources L target mode atoms)
      (Packets.geometry selector (Packets.request sources L target mode atoms)) layout ≤ layout.C)
    (hD : RCFive.NativeResources.driverCap (decompositionOf sources)
      (Packets.request sources L target mode atoms)
      (Packets.geometry selector (Packets.request sources L target mode atoms)) layout printer ≤ V) :
    NativeRows selector compiler sources L target mode atoms printer
      (P1TopDownPaidReusableReserves.workspace printer V)
      (P1TopDownPaidReusableReserves.rewind printer V)
      (P1TopDownPaidReusableReserves.buffer V)
      (RowWidth.rw (M2Of deg (normalizedLiveCount q L)) (U0Of q (normalizedLiveCount q L))
        (exactListWord (C10SupplierRowInput.childList (decompositionOf sources)
          (Packets.live (Packets.request sources L target mode atoms))
          (Packets.request sources L target mode atoms).occurrences)).length)
      (dataList (decompositionOf sources) (Packets.request sources L target mode atoms)
        (Packets.geometry selector (Packets.request sources L target mode atoms)) layout
        (compiler sources L target mode atoms
          (Packets.geometry selector (Packets.request sources L target mode atoms))))
      (LiveRows.fraction sources L target mode atoms).1
      (LiveRows.fraction sources L target mode atoms).2 := by
  refine ⟨layout, rfl, ?_, ?_, rfl, rfl⟩
  · intro d hd
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hd
    exact RCFive.NativeResources.resources _ _ _ layout row.val row.property _ printer V
      ((RCFive.NativeResources.stream_bound _ _ _ layout row.val row.property _).trans hC)
      ((RCFive.NativeResources.driver_bound _ _ _ layout row.val row.property _ printer).trans hD)
  · intro d hd
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp hd
    rw [rowWidth_formula_min _ _ _ layout row.val row.property _ deg hdeg,
      (Packets.geometry selector (Packets.request sources L target mode atoms)).card]
    simp only [RowWidth.rw, M2Of, U0Of, Packets.residual]

end
end NearCubicWires.SourceConstruction.Native
end
