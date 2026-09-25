import Proof.CaseAnalysis.FiveNativeResources
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace RCFive.RowCaps
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open ExtIncidence
open SourceInterfaces P1Closure RepairSource RepairSource.CloseoutFinal CloseoutRowsEstimator
open RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section
variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)

def rawCap := 2^layout.w*(layout.degree*((Packets.pool a F g).length+1)+2)+1

def envelope : Nat :=
  letI := Packets.radix a F g layout
  (Packets.residual F+1)/2+Packets.residual F/2+(Packets.pool a F g).length+
  (exactListWord (Packets.pool a F g)).length+P1Radix.bits (Packets.pool a F g)+
  P1CompactNativeWidth.width (Packets.pool a F g) ((Packets.live F).card+1)+
  ((Packets.live F).card+1)+layout.w+rawCap a F g layout+2^(Packets.live F).card

def headerCap := 2^119*(envelope a F g layout+1)^22*2^(layout.w*((Packets.live F).card+2))

theorem raw_bound (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
    (facts : Packets.PacketFacts a F g r) (ms : List (List (Fin (Packets.pool a F g).length)))
    (hm : ms ∈ Packets.packets a F g r) : (P1CompactNativeFamily.rawWord ms).length ≤ rawCap a F g layout := by
  have hd : ∀ m ∈ ms, m.length ≤ layout.degree := by
    obtain ⟨yi,rfl⟩ := List.mem_ofFn.mp hm
    intro m hm
    exact ((facts.1 yi).2.1 m hm).trans (layout.degreeBound r hr)
  exact (CompactColdCost.raw_word_bound ms layout.degree hd).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Packets.width a F g layout r hr facts ms hm).le) 1)

theorem header_bound (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
    (facts : Packets.PacketFacts a F g r) :
    PCJcc051fd4c1bd4540_Header.budget a F g layout r ≤ headerCap a F g layout := by
  letI := Packets.radix a F g layout
  apply CompactColdCost.budget_bound (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (envelope a F g layout) (Packets.packets a F g r)
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega
  · omega
  · intro ms hm
    exact (Packets.width a F g layout r hr facts ms hm).le
  · intro ms hm
    exact (raw_bound a F g layout r hr facts ms hm).trans (by
      dsimp only [envelope]; generalize (2:Nat)^(Packets.live F).card = v; omega)
  · simp only [Packets.packets,List.length_ofFn,NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput.liveList_length]
    dsimp only [envelope]
    generalize (2:Nat)^(Packets.live F).card = v
    omega

theorem fields_bound (printer : WilliamsAlgorithm)
    (hC : NativeResources.streamCap a F g layout ≤ layout.C)
    (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows) (facts : Packets.PacketFacts a F g r) :
    ∀ i, 2*(PCJ38fbfed565f64139_Row.Frame.fields printer (Packets.datum a F g layout r hr facts) i).length+1 ≤
      2*NativeResources.driverCap a F g layout printer+1 := by
  intro i
  have hb := P1TopDownPaidReusable.input_bound printer (Packets.rowInput a F g layout r hr facts)
    layout.C ((Packets.live F).card+1) (Packets.datum a F g layout r hr facts).select
    ((NativeResources.stream_bound a F g layout r hr facts).trans hC)
    (NativeResources.precision_bound a F g layout r hr facts) i
  have hD := NativeResources.driver_bound a F g layout r hr facts printer
  change 2*(P1TopDownPaidReloadCore.input printer (Packets.rowInput a F g layout r hr facts)
    layout.C ((Packets.live F).card+1) (Packets.datum a F g layout r hr facts).select i).length+1 ≤ _
  omega

private theorem flatMap_bound {α β : Type} (xs : List α) (f : α → List β) (cap : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ cap) : (xs.flatMap f).length ≤ xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem word_bound (printer : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum) (cap : Nat)
    (h : ∀ i, 2*(PCJ38fbfed565f64139_Row.Frame.fields printer d i).length+1 ≤ cap) :
    (d.word printer).length ≤ P1TopDownPaidPayload.tapes printer*cap := by
  have h' := flatMap_bound (List.finRange (P1TopDownPaidPayload.tapes printer))
    (fun i => RepairOrdinary.frame (PCJ38fbfed565f64139_Row.Frame.fields printer d i)) cap (by
      intro i _
      simpa using h i)
  simpa only [List.length_finRange,P1TopDownPaidReusable.Datum.word,
    P1TopDownPaidReusable.word,P1TopDownPaidReusableBody.word,P1TopDownPaidReloadStream.stream,
    PCJ38fbfed565f64139_Row.Frame.fields,PCJeb9c0f0306e9481c_FramingSpec.datumFields] using h'

def chosen (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) :
    PCJd4d1d9d7d1fa4313_Production.RowCaps :=
  let D := NativeResources.driverCap a (r.family a) (geometryOf selector a r) layout printer
  { headerFuel := headerCap a (r.family a) (geometryOf selector a r) layout
    copyCap := 2*D+1
    descriptorReserve := (r.family a).rows.length*P1TopDownPaidPayload.tapes printer*(2*D+1)
    rawReserve := (r.raw selector a).length }

theorem chosen_good (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (hC : NativeResources.streamCap a (r.family a) (geometryOf selector a r) layout ≤ layout.C) :
    PCJd4d1d9d7d1fa4313_Production.RowCaps.Good selector a printer r layout facts (chosen selector a printer r layout) := by
  refine ⟨?_,?_,le_rfl,?_⟩
  · intro row hr
    exact header_bound a (r.family a) (geometryOf selector a r) layout row hr (facts row hr)
  · intro row hr
    exact fields_bound a (r.family a) (geometryOf selector a r) layout printer hC row hr (facts row hr)
  · let ds := dataList a (r.family a) (geometryOf selector a r) layout facts
    let C := (chosen selector a printer r layout).copyCap
    have hd : ∀ d ∈ ds, (d.word printer).length ≤ P1TopDownPaidPayload.tapes printer*C := by
      intro d hd
      obtain ⟨row,_,rfl⟩ := List.mem_map.mp hd
      apply word_bound
      exact fields_bound a (r.family a) (geometryOf selector a r) layout printer hC
        row.val row.property (facts row.val row.property)
    have h := flatMap_bound ds (P1TopDownPaidReusable.Datum.word printer)
      (P1TopDownPaidPayload.tapes printer*C) hd
    simpa only [ds,dataList,List.length_map,List.length_attach,chosen,C,Nat.mul_assoc,PCJ38fbfed565f64139_Cached.descriptorWord] using h

end
end RCFive.RowCaps
