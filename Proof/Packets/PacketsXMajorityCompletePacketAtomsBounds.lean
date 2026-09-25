import Proof.Packets.PacketsXMajorityCompletePacketAtomsMeaning

/-! The actual child-cache source discharges all raw-pair guards of the
physical occurrence-table producer. Its arithmetic alphabet remains C. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section
variable {q L : Nat}

private theorem cache_count (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    (CloseoutRowsUniversal.cacheAtom a gs i).length≤(GS a gs).length := by
  rw [CloseoutRowsUniversal.cache_length]
  have h:=CloseoutRowsRawAtomMeaning.child_range_bound a gs i
  change offset a gs i.val+(children a (gs.get i)).length≤(GS a gs).length at h
  omega

private theorem cache_fits (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    Fits (GS a gs).length (CloseoutRowsUniversal.cacheAtom a gs i) := by
  unfold CloseoutRowsUniversal.cacheAtom
  rw [CloseoutRowsRawAtomCache.source_getElem]
  exact CloseoutRowsRawAtomMeaning.indices_valid a gs i

theorem actual_guards (C w : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (hC : 1≤C) (hchild : PacketMeaning.childCount a F≤C) (hw : 1≤w)
    (hwidth : PacketMeaning.childCount a F+1≤2^w) :
    ∀p∈CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences,
      (p.1++p.2).length≤2^(2*w) ∧ Fits C (p.1++p.2) ∧
        ∀m∈p.1++p.2,m.length≤C := by
  intro p hp
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp
  have hx:=cache_count a (CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)
    (CloseoutRowsUniversal.originalIndex (Packets.live F) F.occurrences i)
  have hc:=cache_count a (CloseoutRowsUniversal.pool (Packets.live F) F.occurrences)
    (CloseoutRowsUniversal.constantIndex (Packets.live F) F.occurrences i)
  have hpow : 2^(w+1)≤2^(2*w) := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]
    change PacketMeaning.childCount a F+1≤2^w at hwidth
    change _≤PacketMeaning.childCount a F at hx hc
    rw [pow_succ] at hpow
    omega
  · intro m hm c hcm
    rcases List.mem_append.mp hm with hm|hm
    · exact (cache_fits a _ _ m hm c hcm).trans_le hchild
    · exact (cache_fits a _ _ m hm c hcm).trans_le hchild
  · intro m hm
    rcases List.mem_append.mp hm with hm|hm
    · exact (CloseoutRowsUniversal.cache_degree a _ _ m hm).trans hC
    · exact (CloseoutRowsUniversal.cache_degree a _ _ m hm).trans hC

theorem actual_run_of_width (C w : Nat) (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (hC : 1≤C) (hocc : F.occurrences.length≤C) (hchild : PacketMeaning.childCount a F≤C)
    (hw : 1≤w) (hwidth : PacketMeaning.childCount a F+1≤2^w) :
    Step machine (budget C (commonReserve C w) F.occurrences.length) DenseAtomBoundary.heads
      (IdentityAtomMaterialize.input C (commonReserve C w)
        (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences) [] [])
      DenseAtomBoundary.heads
      (AddressedAtomMaterialize.paddedA C (commonReserve C w) id
        (CloseoutRowsUniversal.pairs a (Packets.live F) F.occurrences)
        ((PacketMeaning.atoms C a F).map (List.map (maskNat C))) 0) := by
  have h:=actual_guards C w a F hC hchild hw hwidth
  exact actual_run C w a F hocc (fun p hp=>(h p hp).1)
    (fun p hp=>(h p hp).2.1) (fun p hp=>(h p hp).2.2)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtoms
