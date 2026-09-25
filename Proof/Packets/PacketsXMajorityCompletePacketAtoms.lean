import Proof.Packets.PacketsXIdentityAtomGeneralBounded
import Proof.Packets.PacketsXAddressedAtomsNat

/-! Cold occurrence-to-child atom table production from the actual raw pair
cache. Identity addresses and the empty dense bank are physically generated.
Every final entry is the exact ordered normalization of its source pair. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair cacheWord)
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

def polynomials (C : Nat) (cs : List Pair) : List (Ring.Poly Nat) :=
  List.ofFn (fun i : Fin C=>AddressedAtomsNat.answer (cs.getD i.val ([],[])))

theorem identity_table (C : Nat) (cs : List Pair) (hC : cs.length≤C) :
    AddressedAtomsNat.table id cs (List.replicate C []) cs.length=polynomials C cs := by
  apply List.ext_getElem
  · simp only [AddressedAtomsNat.table_length,List.length_replicate,polynomials,List.length_ofFn]
  · intro i hi hj
    have hic : i<C := by simpa only [polynomials,List.length_ofFn] using hj
    have hg : (AddressedAtomsNat.table id cs (List.replicate C []) cs.length).getD i []=
        AddressedAtomsNat.answer (cs.getD i ([],[])) := by
      by_cases hs : i<cs.length
      · exact AddressedAtomsNat.identity_lookup cs (List.replicate C [])
          (by simpa only [List.length_replicate] using hC) i hs
      · rw [AddressedAtomsNat.table_lookup_away id cs (List.replicate C []) i
          (by intro j hj h;change j=i at h;omega) cs.length (Nat.le_refl _),
          List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using hic),
          List.getElem_replicate,List.getD_eq_default cs ([],[]) (by omega)]
        rfl
    rw [List.getD_eq_getElem _ _ hi] at hg
    simpa only [polynomials,List.getElem_ofFn] using hg

theorem mask_table (C : Nat) (cs : List Pair) (hC : cs.length≤C)
    (hf : ∀p∈cs,Fits C (p.1++p.2)) :
    AddressedAtomProgram.table C id cs (List.replicate C []) cs.length=
      (polynomials C cs).map (List.map (maskNat C)) := by
  have h:=AddressedAtomsNat.table_masks C id cs (List.replicate C []) hf cs.length (Nat.le_refl _)
  simp only [List.map_replicate,List.map_nil] at h
  rw [identity_table C cs hC] at h
  exact h

def localMachine := Composition.machine IdentityAtomMaterialize.prepare AddressedAtomCold.machine
def machine := Composition.machine (DenseAtomBoundary.move .right)
  (Composition.machine localMachine (DenseAtomBoundary.move .left))
def budget (C R N : Nat) := 1+1+(IdentityCodeCache.budget R N+4+1+
  AddressedAtomCold.budget C R N+1+1)

theorem run (C w : Nat) (cs : List Pair)
    (hcount : cs.length≤C)
    (hc : ∀p∈cs,(p.1++p.2).length≤2^(2*w))
    (hf : ∀p∈cs,Fits C (p.1++p.2))
    (hd : ∀p∈cs,∀m∈p.1++p.2,m.length≤C) :
    Step machine (budget C (commonReserve C w) cs.length) DenseAtomBoundary.heads
      (IdentityAtomMaterialize.input C (commonReserve C w) cs [] [])
      DenseAtomBoundary.heads
      (AddressedAtomMaterialize.paddedA C (commonReserve C w) id cs
        ((polynomials C cs).map (List.map (maskNat C))) 0) := by
  have hR : C+2≤commonReserve C w := by
    have h:=(Theorem25Completion.CycleDenseAtomCost.reserve_small C w).1
    omega
  have hres:=IdentityAtomGeneralBounded.resources C w cs hcount hc hf hd
  have hstream:=IdentityAtomBounded.stream_reserve C w cs.length hcount
  have prep:=IdentityAtomMaterialize.prepare_run C (commonReserve C w) cs [] []
    (by omega) (by simp) hstream
  have cold:=AddressedAtomMaterialize.cold_padded C (commonReserve C w) id cs hR hcount
    (fun i hi=>by simpa only [id_eq] using hi.trans_le hcount) hres.1
    (by simpa only [IdentityAtomMaterialize.codes_eq] using hstream) hres.2 hf
    (fun p hp=>native_input_reserve C w _ (hf p hp) (hd p hp) (hc p hp))
    (fun p hp=>native_budget_reserve C w _ (hf p hp) (hd p hp) (hc p hp))
  rw [mask_table C cs hcount hf] at cold
  exact (DenseAtomBoundary.raise_run _).seq ((prep.seq cold).seq (DenseAtomBoundary.lower_run _))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
