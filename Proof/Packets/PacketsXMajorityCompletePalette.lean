import Proof.Packets.PacketsXMajorityCompleteLayout

/-! Ten scalar words initialize every private majority tape. Source34 and
the quadratic-width template124 are retained separately. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Palette
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open NormalizedFiniteTransport
noncomputable section

def words (C R N : Nat) : Fin 10→List Bool :=
  ![UnaryTemplate.tape (2*C+3),UnaryTemplate.tape C,UnaryTemplate.tape R,
    List.replicate R true,CompareMachine.word 1,CompareMachine.word N,
    CompareMachine.word ((N+1)/2),frame (SignedSortKey.binary N 0),
    CompareMachine.word (2^N-1),CompareMachine.word (2^N)]
def engineSelect (i : Fin 34) : Option (Fin 10) :=
  if i=13 then some 0 else if i=24 then some 1 else
  if i=31 then some 2 else if i=32 then some 3 else none
def positiveSelect (i : Fin 34) : Option (Fin 10) := if i=28 then some 4 else engineSelect i

def compSelect : Fin 39→Option (Fin 10) :=
  Fin.addCases (m:=34) (n:=5) (motive:=fun _=>Option (Fin 10)) positiveSelect
    ![none,none,none,none,some 5]
def enumSelect : Fin 47→Option (Fin 10) :=
  Fin.addCases (m:=34) (n:=13) (motive:=fun _=>Option (Fin 10)) engineSelect
    ![none,none,none,none,some 5,some 6,none,none,none,none,some 7,none,some 8]
def foldSelect : Fin 38→Option (Fin 10) :=
  Fin.addCases (m:=34) (n:=4) (motive:=fun _=>Option (Fin 10)) engineSelect
    ![none,some 9,none,some 9]
def select : Fin 125→Option (Fin 10) := assemble compSelect enumSelect foldSelect none

def privatePort (i : Fin 123) : Fin 125 :=
  if i.val<34 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def privateSelect (i : Fin 123) := select (privatePort i)

theorem private_not_source (i : Fin 123) : privatePort i≠34 := by
  intro he
  have hv:=congrArg Fin.val he
  dsimp only [privatePort] at hv
  split_ifs at hv <;>simp only [Fin.val_mk] at hv <;>omega

theorem private_not_width (i : Fin 123) : privatePort i≠124 := by
  intro he
  have hv:=congrArg Fin.val he
  dsimp only [privatePort] at hv
  split_ifs at hv <;>simp only [Fin.val_mk] at hv <;>omega

private theorem pad_zeros (S n : Nat) (h : n≤S) :
    ZeroPadding.pad S (List.replicate n false)=List.replicate S false := by
  rw [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1;omega

theorem engine_word (C R N S : Nat) (hRS : R+3≤S) (i : Fin 34) :
    ZeroPadding.pad S ((engineSelect i).elim [] (words C R N))=
      ZeroPadding.pad S (ReusableArithmetic.state C R [] [] i) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hz:=pad_zeros S (R+3) hRS
  have hz1:=pad_zeros S 1 (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  fin_cases i <;>
    simp [engineSelect,words,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,
      NormalizedMultiply.extras,NormalizeCold.data,Normalize.records,SuffixScan.stream,
      Fin.addCases,CompareMachine.word,hp,hz,hz1,hzero,ZeroPadding.pad_zero]


theorem positive_word (C R N S : Nat) (hRS : R+3≤S) (hC : C≤S) (i : Fin 34) :
    ZeroPadding.pad S ((positiveSelect i).elim [] (words C R N))=
      ZeroPadding.pad S (ReusableArithmetic.state C R (([[]] : List (List Nat)).map (maskNat C)) [] i) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hm : (([[]] : List (List Nat)).map (maskNat C))=[List.replicate C false] := by
    simp [maskNat]
  by_cases h28 : i=28
  · subst i
    simp [positiveSelect,words,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,
      NormalizedMultiply.extras,Fin.addCases,hp]
  by_cases h25 : i=25
  · subst i
    simp [positiveSelect,engineSelect,words,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,
      NormalizedMultiply.extras,Fin.addCases,hp,hm,pad_zeros S C hC,hzero]
  rw [positiveSelect,if_neg h28,engine_word C R N S hRS]
  have ht:=VectorAccumulator.tapes_left_outside C R [] []
    (([[]] : List (List Nat)).map (maskNat C)) [] (i.castAdd 2)
    (fun he=>h25 (Fin.castAdd_inj.mp he)) (fun he=>h28 (Fin.castAdd_inj.mp he))
  simp only [VectorAccumulator.tapes_engine] at ht
  exact congrArg (ZeroPadding.pad S) ht

theorem comp_word (C R S : Nat) (ps : List (Ring.Poly Nat)) (hRS : R+3≤S)
    (hC : C≤S) (i : Fin 39) (hi : i≠34) :
    ZeroPadding.pad S ((compSelect i).elim [] (words C R ps.length))=
      ZeroPadding.pad S (compA C R ps 0 [] [] i) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S R (by omega)
  have hz1:=pad_zeros S 1 (by omega)
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  revert hi
  refine Fin.addCases (m:=34) (n:=5) (fun j=>?_) (fun j=>?_) i
  · intro _
    simp only [compSelect,Fin.addCases_left]
    rw [show (j.castAdd 5 : Fin 39)=((j.castAdd 3).castAdd 1).castAdd 1 from rfl]
    simpa only [compA,ComplementPacketStep.A,OrderedPacketStep.A,ArithmeticLookup.A,
      Fin.addCases_left,List.map_nil] using positive_word C R ps.length S hRS hC j
  · intro hj
    fin_cases j
    · exact False.elim (hj rfl)
    all_goals simp [compSelect,compA,ComplementPacketStep.A,OrderedPacketStep.A,
      ArithmeticLookup.A,Fin.addCases,words,CompareMachine.word,hp,hz,hz1,hzero]

theorem enum_word (C R S : Nat) (ps : List (Ring.Poly Nat)) (hRS : R+3≤S) (i : Fin 47) :
    ZeroPadding.pad S ((enumSelect i).elim [] (words C R ps.length))=
      ZeroPadding.pad S (enumCold C R ps i) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S R (by omega)
  have hz1:=pad_zeros S 1 (by omega)
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  refine Fin.addCases (m:=34) (n:=13) (fun j=>?_) (fun j=>?_) i
  · have hn : (j.castAdd 13 : Fin 47)≠34 := by
      intro he;have hv:=congrArg Fin.val he;have hj:=j.isLt;dsimp at hv;omega
    rw [enumCold,Function.update_of_ne hn]
    simp only [enumSelect,Fin.addCases_left]
    rw [show (j.castAdd 13 : Fin 47)=((j.castAdd 3).castAdd 9).castAdd 1 from rfl]
    simpa only [enumerationA,MajorityTermArena.A,OrderedPacketStep.A,ArithmeticLookup.A,
      Fin.addCases_left,List.map_nil] using engine_word C R ps.length S hRS j
  · fin_cases j <;>
      simp [enumSelect,enumCold,enumerationA,MajorityTermArena.A,MajorityTermArena.extras,
        OrderedPacketStep.A,ArithmeticLookup.A,Fin.addCases,Function.update,
        words,CompareMachine.word,hp,hz,hz1,hzero]

theorem fold_word (C R N S : Nat) (hRS : R+3≤S) (i : Fin 38) :
    ZeroPadding.pad S ((foldSelect i).elim [] (words C R N))=
      ZeroPadding.pad S (foldCold C R (2^N) i) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S R (by omega)
  refine Fin.addCases (m:=34) (n:=4) (fun j=>?_) (fun j=>?_) i
  · simp only [foldSelect,Fin.addCases_left]
    rw [show (j.castAdd 4 : Fin 38)=(j.castAdd 3).castAdd 1 from rfl]
    simpa only [foldCold,OrderedPacketFold.tapes,OrderedPacketStep.A,ArithmeticLookup.A,
      Fin.addCases_left,List.map_nil] using engine_word C R N S hRS j
  · fin_cases j <;>
      simp [foldSelect,foldCold,OrderedPacketFold.tapes,OrderedPacketStep.A,
        OrderedPacketStep.bank,PacketVector.bank,ArithmeticLookup.A,Fin.addCases,
        words,CompareMachine.word,hp,hz,hzero]

theorem word_eq (C R S : Nat) (ps : List (Ring.Poly Nat)) (hRS : R+3≤S)
    (hC : C≤S) (i : Fin 125) (hi : i≠34) (hw : i≠124) :
    ZeroPadding.pad S ((select i).elim [] (words C R ps.length))=
      ZeroPadding.pad S (MajorityComplete.input C R ps i) := by
  revert hi hw
  refine Fin.addCases (m:=39) (n:=86) (fun j=>?_) (fun j=>?_) i
  · intro hj _
    simpa only [select,MajorityComplete.input,assemble,Fin.addCases_left] using
      comp_word C R S ps hRS hC j (fun he=>by subst j;exact hj rfl)
  · refine Fin.addCases (m:=47) (n:=39) (fun k=>?_) (fun k=>?_) j
    · intro _ _
      simpa only [select,MajorityComplete.input,assemble,Fin.addCases_left,Fin.addCases_right] using
        enum_word C R S ps hRS k
    · refine Fin.addCases (m:=38) (n:=1) (fun k=>?_) (fun k=>?_) k
      · intro _ _
        simpa only [select,MajorityComplete.input,assemble,Fin.addCases_left,Fin.addCases_right] using
          fold_word C R ps.length S hRS k
      · intro _ hj;fin_cases k
        exact False.elim (hj rfl)

theorem private_word (C R S : Nat) (ps : List (Ring.Poly Nat)) (hRS : R+3≤S)
    (hC : C≤S) (i : Fin 123) :
    ZeroPadding.pad S (NativeFanout.word privateSelect (words C R ps.length) i)=
      ZeroPadding.pad S (MajorityComplete.input C R ps (privatePort i)) :=
  word_eq C R S ps hRS hC (privatePort i) (private_not_source i) (private_not_width i)

structure Fits (C R N S : Nat) : Prop where
  arithmetic : 2*C+5≤S
  reserve : R+3≤S
  assignment : 2*N+1≤S
  codes : 2^N+1≤S

theorem words_length (C R N S : Nat) (h : Fits C R N S) :
    ∀i,(words C R N i).length≤S := by
  obtain ⟨hc,hr,ha,hp⟩:=h
  intro i;fin_cases i <;>simp [words,UnaryTemplate.tape,CompareMachine.word] <;>omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Palette
