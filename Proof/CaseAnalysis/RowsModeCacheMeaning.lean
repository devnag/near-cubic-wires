import Proof.CaseAnalysis.RowsModeCacheHash

/-! The literal cache's exact raw atoms use the original graded label,
original Toeplitz seed, and original occurrence mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape SupplierWalkBridge SupplierToeplitzCore SupplierToeplitz CanonicalFourfoldRowProgram
open CloseoutRowsModeHashMeaning CloseoutRowsModeHashCellMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def parameters (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) : Parameters:=
  ⟨canonicalGradedRank population activeBound,level,C,bits seed.1.1,bits seed.1.2,bits seed.2,
    List.ofFn (fun i=>decide (i∈mask))⟩

theorem hash_original (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (s : State) (hi : s.index<population) :
    hashWord (parameters population activeBound level C mask seed) s=
      bits (toeplitzHash (canonicalGradedLabel population activeBound ⟨s.index,hi⟩) seed):=by
  unfold hashWord parameters label
  rw [CloseoutRowsModeLabel.graded_hash_word population activeBound ⟨s.index,hi⟩ seed]
  exact CloseoutRowsModeHashSource.word_meaning _ _ _ le_rfl

theorem original_mask (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (i : Fin population) :
    readTapeBit (parameters population activeBound level C mask seed).mask i.val=decide (i∈mask):=by
  simp [parameters,readTapeBit,List.getD,i.isLt]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
