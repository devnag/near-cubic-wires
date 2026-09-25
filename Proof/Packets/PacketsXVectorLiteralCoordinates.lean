import Proof.Packets.PacketsXVectorLiteralCoordinateReset
import Proof.Packets.PacketsXVectorCoordinateCollectReset

/-! Complete physical coordinate enumeration. Every final literal vector
coordinate is looked up, substituted once using the constructed dense bank,
and stored at its original ordinal. No callback execution is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def literalCoordinatesFuel (C w population : Nat) :=
  2*commonReserve C w+7+(population+1)*
    (2*PacketBank.lookupBudget (commonReserve C w) population+literalCoordinateFuel C w+10+2*(population+1)+6)+3

theorem literal_coordinates_run (C w d population active depth root ci pi li : Nat)
    (mask : Finset (Fin population)) (seed : ToeplitzSeed (canonicalGradedRank population active))
    (wins : Fin depth → Nat) (hd : depth≤canonicalGradedRank population active)
    (hC : (depth+2*population+2)^2≤C) (hw : 1≤w)
    (hdegree : structuralListCoordinateRawDegree depth wins 0≤d)
    (hfit : (population+1)^d≤2^w) (hfitAtom : population+1≤2^w)
    (hliteral : (population*(2*depth+1)+2)^d≤2^w)
    (left right acc : PacketVector.Packet) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hl : VectorAccumulator.Fits (commonReserve C w) left) (hr : VectorAccumulator.Fits (commonReserve C w) right)
    (hci : ci+1≤commonReserve C w)
    (hs : LiteralLevelState C (commonReserve C w) population root (parameters population active 0 (C+9) mask seed)
      (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth) fields extra) :
    ∃left' right' fields',
      Step (collectedCandidates literalCoordinateCallback) (literalCoordinatesFuel C w population)
        (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (Fin.addCases (A C (commonReserve C w) ci pi li left right acc
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth))
          (PacketVector.bank (commonReserve C w) (List.replicate (population+1) [])) fields extra)
          (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) (population+1)))
        (Fin.addCases (H (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
        (Fin.addCases (A C (commonReserve C w) (population+1) pi li left' right' acc
          (vectorBank C (commonReserve C w) (NormalizedVector.table (canonicalGradedLabel population active) seed wins 0 depth))
          (PacketVector.bank (commonReserve C w) (List.ofFn (fun candidate : Fin (population+1)=>
            (Normalized.structuralMaskedListCoordinate mask (canonicalGradedLabel population active) seed wins 0 candidate).map (maskNat C))))
          fields' extra) (fun _ : Fin 1=>WindowSeed.source (commonReserve C w) (population+1))) ∧
      VectorAccumulator.Fits (commonReserve C w) left' ∧ VectorAccumulator.Fits (commonReserve C w) right' ∧
      LiteralLevelState C (commonReserve C w) population root (parameters population active 0 (C+9) mask seed)
        (denseLevels C population depth (parameters population active 0 (C+9) mask seed) (List.replicate C []) depth) fields' extra := by
  let R:=commonReserve C w
  let label:=canonicalGradedLabel population active
  let p:=parameters population active 0 (C+9) mask seed
  let dense:=denseLevels C population depth p (List.replicate C []) depth
  let ps:=List.ofFn (fun candidate : Fin (population+1)=>
    (Normalized.structuralListPolynomialVector label seed wins 0 candidate).map (maskNat C))
  let answer (i : Nat):=if h : i<population+1 then
    (Normalized.structuralMaskedListCoordinate mask label seed wins 0 ⟨i,h⟩).map (maskNat C) else []
  let Q:=fun (_ : Nat) (l a : PacketVector.Packet) (f : Fin 222 → List Bool) (e : Fin 32 → List Bool)=>
    VectorAccumulator.Fits R l ∧ LiteralLevelState C R population root p dense f e ∧ a=acc ∧ e=extra
  have plen : ps.length=population+1 := List.length_ofFn
  have bank : vectorBank C R (NormalizedVector.table label seed wins 0 depth)=PacketVector.bank R ps := by
    unfold vectorBank
    rw [show NormalizedVector.table label seed wins 0 depth=List.ofFn (Normalized.structuralListPolynomialVector label seed wins 0) from
      NormalizedVector.build_exact label seed wins 0,List.map_ofFn]
    rfl
  have reserve : C+2≤R:=LiteralCacheReuse.reserve_width C w
  have guards (j : Fin (population+1)):=literal_coordinate_guards C w d population active depth mask seed wins j hd hC hdegree hfit hliteral
  have psfit : ∀P∈ps,PacketVector.Fits R P := by
    intro P hP
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hP
    exact packet_fits R _ (guards j).2.1
  have answerfit : ∀i,i<ps.length → VectorAccumulator.Fits R (answer i) := by
    intro i hi
    have hi' : i<population+1 := by omega
    dsimp only [answer]
    rw [dif_pos hi']
    exact (guards ⟨i,hi'⟩).2.2.2
  let E:=2*PacketBank.lookupBudget R population+literalCoordinateFuel C w+10
  have input : CollectReady C R pi li ps answer Q 0
      (A C R 0 pi li left right acc (PacketVector.bank R ps)
        (PacketVector.bank R (List.replicate (population+1) [])) fields extra) := by
    refine ⟨left,right,acc,fields,extra,hr,⟨hl,hs,rfl,rfl⟩,?_⟩
    rw [coordinateTable_zero,plen]
  obtain ⟨output,loop,ready⟩:=coordinate_collect_run literalCoordinateCallback C R pi li (literalCoordinateFuel C w) E
    ps answer Q _ input (by omega) psfit answerfit (by
      intro i hi
      have hi' : i≤population := by omega
      have hm:=Nat.mul_le_mul_right (2*R+5) hi'
      unfold E PacketBank.lookupBudget
      omega) (by
        intro i l a f e hq
        have hi : i.val<population+1 := by have h:=i.isLt;omega
        let j : Fin (population+1):=⟨i.val,hi⟩
        obtain ⟨run,hl',_hr',ready',_bank'⟩:=literal_coordinate_reset_run C w d population active depth pi li mask seed wins j hd hC hw
          hdegree hfit hfitAtom hliteral l a (PacketVector.bank R ps)
          (PacketVector.bank R (coordinateTable ps.length answer i.val)) f e hq.1 hq.2.1.bank hq.2.1.ready
        let P:=Normalized.structuralListPolynomialVector label seed wins 0 j
        let newLeft:=(SubstitutionCall.leftResult (completedAtoms C population active depth mask seed) P []).map (maskNat C)
        let newRight:=(Normalized.structuralMaskedListCoordinate mask label seed wins 0 j).map (maskNat C)
        let fnew:=coordinateFields C R [] (P.map (maskNat C)) newLeft newRight f
        refine ⟨newLeft,a,fnew,e,?_,hl',?_,hq.2.2⟩
        · simpa only [ps,List.getElem_ofFn,answer,dif_pos hi,j,Fin.eta] using run
        · exact level_state_preserved C R population root p dense f _ e hq.2.1 ready'
            (fun k hk _ _ _=>coordinate_fields_retained C R [] _ _ _ f k hk))
  obtain ⟨left',right',acc',fields',extra',hr',hq,rfl⟩:=ready
  obtain ⟨hl',state',ha,he⟩:=hq
  subst acc'
  subst extra'
  have collected:=collected_candidates_run literalCoordinateCallback C R ps.length ci pi li
    (ps.length*(E+2*ps.length+6)+3) left right acc (PacketVector.bank R ps)
    (PacketVector.bank R (List.replicate (population+1) [])) fields extra _ hci loop
  have full : coordinateTable ps.length answer ps.length=
      List.ofFn (fun candidate : Fin (population+1)=>
        (Normalized.structuralMaskedListCoordinate mask label seed wins 0 candidate).map (maskNat C)) := by
    rw [coordinateTable_full,plen]
    simp only [answer,dif_pos,Fin.isLt,Fin.eta]
  rw [full,plen] at collected
  refine ⟨left',right',fields',?_,hl',hr',state'⟩
  rw [bank]
  simpa only [literalCoordinatesFuel,E,R,label,WindowSeed.source,Nat.add_assoc] using collected

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
