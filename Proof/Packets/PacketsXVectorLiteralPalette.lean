import Proof.Packets.PacketsXVectorLiteralWords

/-! Fifteen source words suffice for the entire cold vector arena. The
fanout's finite routing is independent of all numerical parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding CloseoutRowsModeCache
open NearCubicWires.RepairSource.ProjectionNormalization
noncomputable section

def coldPalette (C R M root depth : Nat) (p : Parameters) : Fin 15 → List Bool :=
  ![UnaryTemplate.tape (2*C+3),UnaryTemplate.tape C,UnaryTemplate.tape R,
    List.replicate R true,List.replicate root true,List.replicate p.rank true,
    p.lower,p.upper,p.translation,CompareMachine.word p.rank,p.mask,
    List.replicate p.C true,CompareMachine.word depth,CompareMachine.word (C+9),CompareMachine.word M]

def coldFieldSelect (j : Fin 222) : Option (Fin 15) :=
  if j=117 then some 4 else if j=119 then some 5 else
  if j=120 then some 6 else if j=121 then some 7 else
  if j=122 then some 8 else if j=123 then some 9 else
  if j=124 then some 10 else if j=126 then some 11 else
  if j=143 then some 12 else if j=149 then some 13 else
  if j=150 then some 14 else none

def coldEngineSelect (j : Fin 34) : Option (Fin 15) :=
  if j=13 then some 0 else if j=24 then some 1 else
  if j=31 then some 2 else if j=32 then some 3 else none

def coldSelect : Fin 299 → Option (Fin 15) :=
  Fin.addCases (m:=298) (n:=1) (motive:=fun _=>Option (Fin 15))
    (Fin.addCases (m:=296) (n:=2) (motive:=fun _=>Option (Fin 15))
      (Fin.addCases (m:=264) (n:=32) (motive:=fun _=>Option (Fin 15))
        (Fin.addCases (m:=256) (n:=8) (motive:=fun _=>Option (Fin 15))
          (Fin.addCases (m:=34) (n:=222) (motive:=fun _=>Option (Fin 15))
            coldEngineSelect coldFieldSelect) (fun _=>none)) (fun _=>none)) (fun _=>none)) (fun _=>none)

private theorem pad_zeros (S n : Nat) (h : n ≤ S) :
    ZeroPadding.pad S (List.replicate n false)=List.replicate S false := by
  rw [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1;omega

theorem cold_fields_palette (C R M root depth S : Nat) (p : Parameters)
    (hRS : R ≤ S) (hS : 1 ≤ S) (j : Fin 222) :
    ZeroPadding.pad S ((coldFieldSelect j).elim [] (coldPalette C R M root depth p)) =
      ZeroPadding.pad S (coldFields C R M root depth p j) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs hRS
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S R hRS
  have hz1:=pad_zeros S 1 hS
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  by_cases h106 : j=106
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h117 : j=117
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h118 : j=118
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h119 : j=119
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h120 : j=120
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h121 : j=121
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h122 : j=122
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h123 : j=123
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h124 : j=124
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h126 : j=126
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h143 : j=143
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h149 : j=149
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  by_cases h150 : j=150
  · subst j
    simp [coldFieldSelect,coldFields,coldPalette,WindowSeed.source,CompareMachine.word,hp,hz,hz1,hzero]
  simp [coldFieldSelect,coldFields,h106,h117,h118,h119,h120,h121,h122,h123,h124,h126,h143,h149,h150,hz,hzero]

theorem cold_engine_palette (C R M root depth S : Nat) (p : Parameters)
    (hRS : R+3 ≤ S) (j : Fin 34) :
    ZeroPadding.pad S ((coldEngineSelect j).elim [] (coldPalette C R M root depth p)) =
      ZeroPadding.pad S (ReusableArithmetic.state C R [] [] j) := by
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs (by omega)
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S (R+3) hRS
  have hz1:=pad_zeros S 1 (by omega)
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  fin_cases j <;>
    simp [coldEngineSelect,coldPalette,ReusableArithmetic.state,ReusableArithmetic.bank,
      ReusableArithmetic.padded,ReusableArithmetic.data,NormalizedMultiply.data,
      NormalizedMultiply.extras,NormalizeCold.data,Normalize.records,SuffixScan.stream,
      Fin.addCases,CompareMachine.word,hp,hz,hz1,hzero,ZeroPadding.pad_zero]

theorem cold_palette_data (C R M root depth S : Nat) (p : Parameters)
    (hRS : R+3 ≤ S) :
    (fun i=>ZeroPadding.pad S (NativeFanout.word coldSelect (coldPalette C R M root depth p) i)) =
      (fun i=>ZeroPadding.pad S (coldData C R (coldFields C R M root depth p) (coldExtra R) i)) := by
  have hR : R ≤ S := by omega
  have hS : 1 ≤ S := by omega
  have hp (xs : List Bool) : ZeroPadding.pad S (ZeroPadding.pad R xs)=ZeroPadding.pad S xs :=
    MatrixBucketRootPower.pad_pad R S xs hR
  have hzero : ZeroPadding.pad S []=List.replicate S false := by simp [ZeroPadding.pad]
  have hz:=pad_zeros S R hR
  have hzlog:=pad_zeros S (R+1) (by omega)
  have hz1:=pad_zeros S 1 hS
  simp only [List.replicate_succ,List.replicate_zero] at hz1
  funext i
  refine Fin.addCases (m:=298) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=296) (n:=2) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=264) (n:=32) (fun l=>?_) (fun l=>?_) k
      · refine Fin.addCases (m:=256) (n:=8) (fun q=>?_) (fun q=>?_) l
        · refine Fin.addCases (m:=34) (n:=222) (fun r=>?_) (fun r=>?_) q
          · simpa only [NativeFanout.word,coldSelect,coldData,A,VectorController.A,
              Fin.addCases_left] using cold_engine_palette C R M root depth S p hRS r
          · simpa only [NativeFanout.word,coldSelect,coldData,A,VectorController.A,
              Fin.addCases_left,Fin.addCases_right] using cold_fields_palette C R M root depth S p hR hS r
        · fin_cases q <;> simp [NativeFanout.word,coldSelect,coldData,A,VectorController.A,
            VectorController.extraTapes,Fin.addCases,CompareMachine.word,hp,hz,hz1,hzero]
      · simp only [NativeFanout.word,coldSelect,coldData,A,Fin.addCases_left,Fin.addCases_right,coldExtra]
        split_ifs <;> simp [hz,hzlog,hzero]
    · simp [NativeFanout.word,coldSelect,coldData,Fin.addCases_left,Fin.addCases_right,hz,hzero]
  · simp [NativeFanout.word,coldSelect,coldData,Fin.addCases_right,hz,hzero]

theorem cold_palette_length (C R M root depth S : Nat) (p : Parameters)
    (h : ColdWordBounds C R M root depth p) (hRS : R+3 ≤ S) (hCS : 2*C+5 ≤ S) :
    ∀j,(coldPalette C R M root depth p j).length ≤ S := by
  have hR : R ≤ S := by omega
  have hrank:=h.rank
  have hwidth:=h.width
  have hroot:=h.root
  have hdepth:=h.depth
  have hM:=h.population
  have hlo:=h.lower
  have hhi:=h.upper
  have ht:=h.translation
  have hm:=h.mask
  have hc:=h.codeWidth
  intro j;fin_cases j <;> simp [coldPalette,UnaryTemplate.tape,CompareMachine.word] <;> omega

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
