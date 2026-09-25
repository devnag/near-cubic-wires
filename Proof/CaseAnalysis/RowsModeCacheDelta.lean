import Proof.CaseAnalysis.RowsModeCacheMeaning

/-! Both delta literal families are the original sibling/child cells.
The negative child's constant survives even on a masked-out coordinate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape SupplierWalkBridge SupplierToeplitzCore SupplierToeplitz CanonicalFourfoldRowProgram
open CloseoutRowsModeHashMeaning CloseoutRowsModeHashCellMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sibling_original (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (s : State)
    (hi : s.index < population) (hl : level < canonicalGradedRank population activeBound) :
    (guarded (parameters population activeBound level C mask seed) s).sibling=
      decide (toeplitzHash (canonicalGradedLabel population activeBound ⟨s.index,hi⟩) seed∈
        siblingPrefixCell (canonicalGradedRank population activeBound) level):=by
  unfold guarded
  rw [hash_original _ _ _ _ _ _ _ hi]
  exact sibling_meaning _ _ hl

theorem child_original (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (s : State)
    (hi : s.index < population) (hl : level < canonicalGradedRank population activeBound) :
    (guarded (parameters population activeBound level C mask seed) s).child=
      decide (toeplitzHash (canonicalGradedLabel population activeBound ⟨s.index,hi⟩) seed∈
        zeroPrefixCell (canonicalGradedRank population activeBound) (level+1)):=by
  unfold guarded
  rw [hash_original _ _ _ _ _ _ _ hi]
  exact child_meaning _ _ hl

theorem sibling_atom (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (s : State)
    (hi : s.index < population) (hl : level < canonicalGradedRank population activeBound) :
    let p:=parameters population activeBound level C mask seed
    let t:=selected 1 p (guarded p s)
    CloseoutRowsModeLiteralMeaning.polynomial t.neg t.var t.index=
      if decide (toeplitzHash (canonicalGradedLabel population activeBound ⟨s.index,hi⟩) seed∈
        siblingPrefixCell (canonicalGradedRank population activeBound) level) then
        structuralMaskedCoordinate mask ⟨s.index,hi⟩ else structuralGF2Zero:=by
  dsimp only
  change CloseoutRowsModeLiteralMeaning.polynomial false
    ((guarded (parameters population activeBound level C mask seed) s).sibling&&
      readTapeBit (parameters population activeBound level C mask seed).mask s.index) s.index=_
  rw [sibling_original _ _ _ _ _ _ _ hi hl,original_mask population activeBound level C mask seed ⟨s.index,hi⟩]
  exact CloseoutRowsModeLiteralMeaning.positive mask ⟨s.index,hi⟩ _

theorem child_atom (population activeBound level C : Nat) (mask : Finset (Fin population))
    (seed : ToeplitzSeed (canonicalGradedRank population activeBound)) (s : State)
    (hi : s.index < population) (hl : level < canonicalGradedRank population activeBound) :
    let p:=parameters population activeBound level C mask seed
    let t:=selected 2 p (guarded p s)
    CloseoutRowsModeLiteralMeaning.polynomial t.neg t.var t.index=
      if decide (toeplitzHash (canonicalGradedLabel population activeBound ⟨s.index,hi⟩) seed∈
        zeroPrefixCell (canonicalGradedRank population activeBound) (level+1)) then
        structuralGF2Not (structuralMaskedCoordinate mask ⟨s.index,hi⟩) else structuralGF2Zero:=by
  dsimp only
  change CloseoutRowsModeLiteralMeaning.polynomial
    ((guarded (parameters population activeBound level C mask seed) s).child)
    ((guarded (parameters population activeBound level C mask seed) s).child&&
      readTapeBit (parameters population activeBound level C mask seed).mask s.index) s.index=_
  rw [child_original _ _ _ _ _ _ _ hi hl,original_mask population activeBound level C mask seed ⟨s.index,hi⟩]
  exact CloseoutRowsModeLiteralMeaning.negative mask ⟨s.index,hi⟩ _

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
