import Proof.CaseAnalysis.FiveLiveSetCaps
import Proof.Rows.HeaderBudget
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace RCFive.NativeResources
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram
open SourceInterfaces P1Closure RepairSource RepairSource.CloseoutFinal
open CloseoutRowsEstimator CompetitorSelectedCount RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows) (facts : Packets.PacketFacts a F g r)

def beta := CompactBounds.radix a (Packets.live F) F.occurrences
def degree := min layout.degree (Packets.pool a F g).length
def precision := beta a F * (degree a F g layout * ((Packets.live F).card+1)) + ((Packets.live F).card+1)
def cutsCap := 2^(2*((Packets.live F).card+layout.w*((Packets.live F).card+2)))
def streamCap := cutsCap a F g layout * (Packets.residual F+2) * (2*precision a F g layout+3)

theorem dimensions :
    (Packets.rowInput a F g layout r hr facts).d = (Packets.residual F+1)/2 ∧
    (Packets.rowInput a F g layout r hr facts).p = precision a F g layout ∧
    (Packets.rowInput a F g layout r hr facts).odd = decide (Packets.residual F%2=1) ∧
    (EquationRow.request (Packets.rowInput a F g layout r hr facts)).p = precision a F g layout+1 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem precision_bound : (Packets.live F).card+1 ≤
    (EquationRow.request (Packets.rowInput a F g layout r hr facts)).p := by
  rw [(dimensions a F g layout r hr facts).2.2.2]
  unfold precision
  omega

theorem fields : Scan.countFields (Packets.rowInput a F g layout r hr facts) = Packets.residual F+2 := by
  obtain ⟨hd,_,ho,_⟩ := dimensions a F g layout r hr facts
  unfold Scan.countFields
  rw [hd,ho]
  by_cases h : Packets.residual F%2=1 <;> simp [h] <;> omega

theorem cuts_bound : (Packets.rowInput a F g layout r hr facts).cuts.length ≤ cutsCap a F g layout := by
  letI := Packets.radix a F g layout
  let bank := ExtIncidence.NativeRowInput.bank (Packets.packets a F g r)
  have hw := ExtIncidence.NativeRowInput.bank_width (Packets.packets a F g r) layout.w
    (Packets.width a F g layout r hr facts)
  have hb : bank.length ≤ 2^(Packets.live F).card := by
    simp only [bank,ExtIncidence.NativeRowInput.bank,Packets.packets,List.length_map,
      List.length_ofFn,C10SupplierRowInput.liveList_length,le_refl]
  have hc := CloseoutRawRows.raw_cuts_bound (Packets.pool a F g) (Packets.live F).card
    layout.w bank hb hw layout.positiveWidth
  have hn := P1CompactCloseoutRowsSharedDigits.batch_perm (Packets.pool a F g)
    ((Packets.live F).card+1) layout.w bank hw
  have ho := CloseoutRowsSharedDigits.batch_perm (Packets.pool a F g)
    ((Packets.live F).card+1) layout.w bank hw
  change (bank.flatMap (P1CompactCloseoutRowsSharedDigits.cuts (Packets.pool a F g)
    ((Packets.live F).card+1) layout.w)).length ≤ _
  rw [hn.length_eq,RowPowerBinLift.batch_length]
  rw [ho.length_eq,RowPowerBinLift.batch_length] at hc
  exact hc

theorem stream_bound :
    (Header.stream (Packets.rowInput a F g layout r hr facts)).length ≤ streamCap a F g layout := by
  rw [PCJ45bee56da9f34d5a_HeaderBudget.stream_length,fields,
    (dimensions a F g layout r hr facts).2.1]
  have hcuts := cuts_bound a F g layout r hr facts
  unfold streamCap
  nlinarith [Nat.mul_le_mul_right ((Packets.residual F+2)*(2*precision a F g layout+3)) hcuts]

/-- Converts the single driver estimate into the actual seven-field Resources consumer. -/
theorem resources (printer : WilliamsAlgorithm) (D : Nat)
    (hC : (Header.stream (Packets.rowInput a F g layout r hr facts)).length ≤ layout.C)
    (hD : Driver.value printer
      (Packets.rowInput a F g layout r hr facts).d (Packets.rowInput a F g layout r hr facts).p
      (Packets.rowInput a F g layout r hr facts).cuts.length layout.C ≤ D) :
    Resources printer (P1TopDownPaidReusableReserves.buffer D)
      (P1TopDownPaidReusableReserves.rewind printer D)
      (P1TopDownPaidReusableReserves.workspace printer D) (Packets.datum a F g layout r hr facts) := by
  have hQ := precision_bound a F g layout r hr facts
  obtain ⟨hR,hB,hBR,hS,hBS⟩ := P1TopDownPaidReusableReserves.capacities printer
    (Packets.rowInput a F g layout r hr facts) layout.C ((Packets.live F).card+1) D hC hQ hD
  exact ⟨hC,hQ,hR,hB,hBR,hS,hBS⟩

def driverCap (printer : WilliamsAlgorithm) := Driver.value printer ((Packets.residual F+1)/2)
  (precision a F g layout) (cutsCap a F g layout) layout.C

theorem driver_bound (printer : WilliamsAlgorithm) :
    Driver.value printer (Packets.rowInput a F g layout r hr facts).d
      (Packets.rowInput a F g layout r hr facts).p
      (Packets.rowInput a F g layout r hr facts).cuts.length layout.C ≤ driverCap a F g layout printer := by
  rw [(dimensions a F g layout r hr facts).1,(dimensions a F g layout r hr facts).2.1]
  unfold driverCap Driver.value
  gcongr
  exact cuts_bound a F g layout r hr facts


end
end RCFive.NativeResources
