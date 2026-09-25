import Proof.CaseAnalysis.RowsModeLiteralMeaning

/-! Original occurrence labels are advanced by the existing physical binary
counter. One spare bit pays the last population boundary without wraparound;
the original Toeplitz rank reads only its original lower coordinates. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLabel
open LocalBitMultitape SignedSortKey ExtDecompositionBatch CloseoutRowsModeHashMeaning
open SupplierWalkBridge
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem advance (rank n C : Nat) (hn : n<2^rank) (hC : rank+1≤C) :
    Step (Rewind.machine BinaryIncrement.machine) (2*rank+4)
      (RankScalar.scalarConfig 0 (binary (rank+1) n) 0 (List.replicate C false) 0).heads
      (RankScalar.scalarConfig 0 (binary (rank+1) n) 0 (List.replicate C false) 0).tapes
      (RankScalar.scalarConfig 3 (binary (rank+1) (n+1)) 0 (List.replicate C false) 0).heads
      (RankScalar.scalarConfig 3 (binary (rank+1) (n+1)) 0 (List.replicate C false) 0).tapes:=by
  have hp:0<2^rank:=by positivity
  have hfit:n+1<2^(rank+1):=by rw [pow_succ];omega
  obtain ⟨r,hr,rf⟩:=MemoryEmitCounter.increment_run (rank+1) n C hfit hC
  have raw:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa only [show 2*(rank+1)+2=2*rank+4 by omega,RankScalar.scalarConfig] using raw

theorem read_binary (width n i : Nat) (hi : i<width) :
    readTapeBit (binary width n) i=n.testBit i:=by
  rw [←RepairSource.VerifierDecoding.fixedBits_binary]
  simp [RepairSource.VerifierEncoding.fixedBits,readTapeBit,List.getD,hi]

theorem graded_read (population activeBound : Nat) (n : Fin population)
    (i : Fin (canonicalGradedRank population activeBound)) :
    readTapeBit (binary (canonicalGradedRank population activeBound+1) n.val) i.val=
      readTapeBit (bits (canonicalGradedLabel population activeBound n)) i.val:=by
  apply field_injective
  rw [read_binary _ _ _ (by omega),read_bits]
  rfl

theorem fold_congr (rank row : Nat) (left right lower upper : List Bool) (cs : List Nat) (acc : Bool)
    (hread : ∀ i<rank,readTapeBit left i=readTapeBit right i) (hcs : ∀ i∈cs,i<rank) :
    CloseoutRowsModeHashBit.fold row left lower upper cs acc=
      CloseoutRowsModeHashBit.fold row right lower upper cs acc:=by
  induction cs generalizing acc with
  | nil=>rfl
  | cons i cs ih=>
    have hi:=hread i (hcs i (by simp))
    simp only [CloseoutRowsModeHashBit.fold,List.foldl_cons]
    rw [show CloseoutRowsModeHashBit.term row i left lower upper=CloseoutRowsModeHashBit.term row i right lower upper by
      simp only [CloseoutRowsModeHashBit.term,hi]]
    exact ih _ (fun j hj=>hcs j (by simp [hj]))

theorem graded_hash_word (population activeBound : Nat) (n : Fin population)
    (seed : SupplierToeplitzCore.ToeplitzSeed (canonicalGradedRank population activeBound)) (depth : Nat) :
    CloseoutRowsModeHashLoop.word (canonicalGradedRank population activeBound) depth
      (binary (canonicalGradedRank population activeBound+1) n.val) (bits seed.1.1) (bits seed.1.2) (bits seed.2)=
      CloseoutRowsModeHashLoop.word (canonicalGradedRank population activeBound) depth
        (bits (canonicalGradedLabel population activeBound n)) (bits seed.1.1) (bits seed.1.2) (bits seed.2):=by
  unfold CloseoutRowsModeHashLoop.word
  apply List.flatMap_congr
  intro row hrow
  congr 1
  apply fold_congr (canonicalGradedRank population activeBound)
  · intro i hi
    exact graded_read population activeBound n ⟨i,hi⟩
  · intro i hi
    exact List.mem_range.mp hi

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLabel
