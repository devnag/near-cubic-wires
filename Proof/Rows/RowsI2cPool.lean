import Proof.Assembly.ColdSource
import Proof.SourceAssembly.PoolDonorCompatible

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Cold's paid bound (copy of `ColdCompatible`'s `ColdBudget`, renamed) -/

namespace RowsConstruction.I2c.ColdBudget
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtDecompositionBatch.Cold
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairOrdinary.DecompositionSource NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open NearCubicWires.RepairSource.ProjectionNormalization
variable (a:DecompositionAlgorithm)

theorem round_sum_bound {q:ℕ} (C:ℕ) (occ:List (SupportedNormalizedGate q))
    (hb:∀g∈occ,bodyCost a q g<C):roundSum a C occ≤occ.length*(4*C+9):=by
  induction occ with
  | nil=>simp [roundSum]
  | cons g occ ih=>
    have head:=hb g (by simp)
    have tail:=ih (fun k hk=>hb k (by simp [hk]))
    simp only [roundSum,List.map_cons,List.sum_cons,List.length_cons,roundCost]
    change 2*bodyCost a q g+2+1+(2*C+4)+2+roundSum a C occ≤_
    nlinarith

theorem batch_bound {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    batchBudget a (SourceEnvelope.capacity a P) occ top≤64*(SourceEnvelope.capacity a P+1)^2:=by
  let C:=SourceEnvelope.capacity a P
  obtain ⟨body,hn,hh,hb,_hc,header⟩:=SourceEnvelope.actual_capacity a occ top P hq hi
  obtain ⟨qU,nU,bU,_,_⟩:=SourceEnvelope.actual_bounds a occ top P hq hi
  have cover:=SourceEnvelope.capacity_covers a P
  have uc:SourceEnvelope.aggregate a P≤C:=by dsimp [C];nlinarith
  have qc:q≤C:=qU.trans uc
  have nc:occ.length≤C:=nU.trans uc
  have bc:B a occ≤C:=bU.trans uc
  have topc:top.length≤C:=by
    have h:=SourceEnvelope.source_position a occ top P hi
    rw [segment_length] at h
    have f:=word_le_frame top
    dsimp only [C]
    omega
  have sum:roundSum a C occ≤C*(4*C+9):=
    (round_sum_bound a C occ body).trans (Nat.mul_le_mul_right _ nc)
  have prod:=Nat.mul_le_mul qc bc
  change batchBudget a C occ top≤64*(C+1)^2
  unfold batchBudget Prelude.occurrenceBudget Prelude.budget PreludeHeader.budget loopCost FinalLayout.finalCost
  change (2*PCPPQueryNatural.budget occ.length+2*C+7+1+(2*top.length+3))+1+
    (roundSum a C occ+occ.length+3)+1+
    ((bodyWord a occ).length+(6*q+15)*B a occ+2*PCPPNativeNaturalAppend.budget (B a occ)+4*C+28)≤_
  change PCPPNativeNaturalAppend.budget (B a occ)≤C at hh
  change (bodyWord a occ).length≤C at hb
  change PCPPQueryNatural.budget occ.length<C at header
  nlinarith

theorem capacity_square (P:ℕ):
    (SourceEnvelope.capacity a P+1)^2≤(SourceEnvelope.coefficient a+1)^2*
      (P+2)^(2*SourceEnvelope.degree a+2):=by
  have one:1≤(P+1)^SourceEnvelope.degree a:=Nat.one_le_pow _ _ (by omega)
  have le:SourceEnvelope.capacity a P+1≤
      (SourceEnvelope.coefficient a+1)*(P+1)^SourceEnvelope.degree a:=by
    unfold SourceEnvelope.capacity
    nlinarith
  have sq:=Nat.pow_le_pow_left le 2
  have powers:((P+1)^SourceEnvelope.degree a)^2≤(P+2)^(2*SourceEnvelope.degree a+2):=by
    rw [←pow_mul]
    exact (Nat.pow_le_pow_left (by omega : P+1≤P+2) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [mul_pow] at sq
  exact sq.trans (Nat.mul_le_mul_left _ powers)

def runtimeCoefficient:=DimensionPolynomial.coefficient (SourceEnvelope.degree a)
  (SourceEnvelope.coefficient a)+128*(SourceEnvelope.coefficient a+1)^2
def runtimeDegree:=2*SourceEnvelope.degree a+2

theorem budget_bound {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    Cold.budget a P occ top≤runtimeCoefficient a*(P+2)^runtimeDegree a:=by
  have b:=batch_bound a P occ top hq hi
  have factory:=DimensionPolynomial.budget_bound (SourceEnvelope.degree a) (SourceEnvelope.coefficient a) P
  have square:=capacity_square a P
  have scaled:=Nat.mul_le_mul_left 128 square
  unfold Cold.budget Cold.entryBudget runtimeCoefficient runtimeDegree
  nlinarith

end RowsConstruction.I2c.ColdBudget

/-! ## 2. The paired pool writer followed by Cold (copy of `PoolColdCompatible`, renamed) -/

namespace RowsConstruction.I2c.PoolCold
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource SupplierPipeline RepairRepresentation VerifierDecoding P1Closure
open scoped BigOperators
attribute [local irreducible] PoolEntryOccurrence.machine Cold.machine

abbrev sourcePort (a : DecompositionAlgorithm) := Cold.port a (str a)
def slots (a : DecompositionAlgorithm) (i : Fin (Cold.tapes a)) :
    Fin (132+Cold.tapes a) :=
  if i=sourcePort a then (61 : Fin 132).castAdd _ else i.natAdd 132

theorem slots_injective (a : DecompositionAlgorithm) : Function.Injective (slots a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv with hi hj hj
  · exact hi.trans hj.symm
  · simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
  · simp only [Fin.val_castAdd,Fin.val_natAdd] at hv;omega
  · apply Fin.ext
    simp only [Fin.val_natAdd] at hv
    omega

noncomputable def machine (a : DecompositionAlgorithm) := Composition.machine
  (TapeEmbedding.machine (Cold.tapes a) PoolEntryLoop.machine)
  (RecoveryFocus.machine (slots a) (Cold.machine a))

noncomputable def start {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w : Nat) (top : List Bool) :=
  RepeatMachine.cfg 0
    (PoolEntryLoop.cfg live occ B w 0 (natWord (2*occ.length)++RepairOrdinary.frame top)) occ.length 1

noncomputable def finish {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w : Nat) (top : List Bool) :=
  RepeatMachine.cfg 3
    (PoolEntryLoop.cfg live occ B w occ.length (segment (CloseoutRowsUniversal.pool live occ) top))
    occ.length 1

def coldHeads (a : DecompositionAlgorithm) := Cold.heads a 0
def coldData (a : DecompositionAlgorithm) (P q : Nat) := Cold.data a P q []

theorem source_heads (a : DecompositionAlgorithm) (pos : Nat) :
    Cold.heads a pos (sourcePort a)=pos := by
  simp [Cold.heads,sourcePort,Cold.port,
    Cold.old,Cold.port,Cold.old,Cold.heads,str,live,ex]

theorem source_data (a : DecompositionAlgorithm) (P q : Nat) (word : List Bool) :
    Cold.data a P q word (sourcePort a)=word := by
  simp [Cold.data,sourcePort,Cold.port,
    Cold.old,Cold.port,Cold.old,Cold.data,str,live,ex]

theorem sourcePort_val (a : DecompositionAlgorithm) : (sourcePort a).val=SB a := by
  simp [sourcePort,Cold.port,Cold.old,str,live,ex]

theorem cold_heads_other (a : DecompositionAlgorithm) (pos : Nat)
    (i : Fin (Cold.tapes a)) (hi : i≠sourcePort a) :
    coldHeads a i=Cold.heads a pos i := by
  have hn : i.val≠SB a := by
    intro h
    apply hi
    exact Fin.ext (h.trans (sourcePort_val a).symm)
  simp only [coldHeads,Cold.heads,if_neg hn]

theorem cold_data_other (a : DecompositionAlgorithm) (P q : Nat) (word : List Bool)
    (i : Fin (Cold.tapes a)) (hi : i≠sourcePort a) :
    coldData a P q i=Cold.data a P q word i := by
  have hn : i.val≠SB a := by
    intro h
    apply hi
    exact Fin.ext (h.trans (sourcePort_val a).symm)
  simp only [coldData,Cold.data,if_neg hn]

theorem run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ H O, Step (machine a)
      (PoolEntryLoop.budget occ.length B q w+1+
        RowsConstruction.I2c.ColdBudget.runtimeCoefficient a*(P+2)^RowsConstruction.I2c.ColdBudget.runtimeDegree a)
      (Fin.addCases (start live occ B w top).heads (coldHeads a))
      (Fin.addCases (start live occ B w top).tapes (coldData a P q))
      (dockH (slots a) (Fin.addCases (finish live occ B w top).heads (coldHeads a)) H)
      (install (slots a) (Fin.addCases (finish live occ B w top).tapes (coldData a P q)) O) ∧
      O (Cold.port a (cch a))=exactListWord (GS a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (cch a))=0 ∧
      O (Cold.port a (cnt a))=countWord a (CloseoutRowsUniversal.pool live occ) ∧
      H (Cold.port a (cnt a))=(countWord a (CloseoutRowsUniversal.pool live occ)).length ∧
      O (sourcePort a)=segment (CloseoutRowsUniversal.pool live occ) top ∧
      H (sourcePort a)=(segment (CloseoutRowsUniversal.pool live occ) top).length ∧
      O (Cold.port a (tot a))=UnaryTemplate.tape (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) ∧
      H (Cold.port a (tot a))=1 ∧
      O (Cold.port a (dom a))=UnaryTemplate.tape q ∧ H (Cold.port a (dom a))=1 ∧
      O (Cold.port a (scr a))=List.replicate (ExtDecompositionBatch.B a (CloseoutRowsUniversal.pool live occ)) false ∧
      H (Cold.port a (scr a))=0 ∧
      O (Cold.port a (drv a))=List.replicate (SourceEnvelope.capacity a P) true ∧
      H (Cold.port a (drv a))=0 ∧
      O (Cold.port a (wsp a))=List.replicate (SourceEnvelope.capacity a P+1) false ∧
      H (Cold.port a (wsp a))=0 := by
  obtain ⟨r,hr,hfinal,_hs⟩ := PoolEntryLoop.segment_run live occ B w top hw hqw hb hm
  have writer : Step PoolEntryLoop.machine (PoolEntryLoop.budget occ.length B q w)
      (start live occ B w top).heads (start live occ B w top).tapes
      (finish live occ B w top).heads (finish live occ B w top).tapes :=
    Step.of_run hr (congrArg Configuration.heads hfinal) (congrArg Configuration.tapes hfinal)
  obtain ⟨H,O,source,fields⟩ := Cold.cold_run a P (CloseoutRowsUniversal.pool live occ) top hqP hi
  have paid := source.enlarge
    (RowsConstruction.I2c.ColdBudget.budget_bound a P (CloseoutRowsUniversal.pool live occ) top hqP hi)
  have middle := writer.embed (coldHeads a) (coldData a P q)
  have last := paid.dock (slots a) (slots_injective a)
    (Fin.addCases (finish live occ B w top).heads (coldHeads a))
    (Fin.addCases (finish live occ B w top).tapes (coldData a P q))
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_heads]
        rfl
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_heads_other a _ j hj)
    (by
      intro j
      by_cases hj : j=sourcePort a
      · subst j
        rw [slots,if_pos rfl,Fin.addCases_left,source_data]
        change ZeroPadding.pad 0 (PoolEntryBaseline.bank live B w _ _ 61)=_
        rw [ZeroPadding.pad_zero,PoolEntryBaseline.bank_output]
      · rw [slots,if_neg hj,Fin.addCases_right]
        exact cold_data_other a P q _ j hj)
  exact ⟨H,O,middle.seq last,fields⟩

end RowsConstruction.I2c.PoolCold

/-! ## 3. The cache port and the rewound domain port (copy of `SourceCache.ready_run`, renamed) -/

namespace RowsConstruction.I2c.PoolReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open RowsConstruction.I2c
noncomputable section

abbrev tapes (a : DecompositionAlgorithm) := 132+Cold.tapes a
def cachePort (a : DecompositionAlgorithm) : Fin (tapes a) :=
  PoolCold.slots a (Cold.port a (cch a))
def domainPort (a : DecompositionAlgorithm) : Fin (tapes a) :=
  PoolCold.slots a (Cold.port a (dom a))

theorem cache_ne_domain (a : DecompositionAlgorithm) : cachePort a ≠ domainPort a := by
  intro h
  have he := PoolCold.slots_injective a h
  have hv := congrArg Fin.val he
  simp only [Cold.port,Cold.old,live,cch,dom,ex,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def directions (a : DecompositionAlgorithm) (i : Fin (tapes a)) : HeadMove :=
  if i=domainPort a then .left else .stay

def readyMachine (a : DecompositionAlgorithm) := Composition.machine (PoolCold.machine a)
  (DecompositionCountPosition.move (directions a))

def budget {q : Nat} (a : DecompositionAlgorithm) (occ : List (SupportedNormalizedGate q))
    (B w P : Nat) := PoolEntryLoop.budget occ.length B q w+1+
      ColdBudget.runtimeCoefficient a*(P+2)^ColdBudget.runtimeDegree a+2

/-- **The child cache from the writer's start bank.** Cache port: `exactListWord (childList a live occ)`, head `0`; domain
port: `UnaryTemplate.tape q`, head `0`. -/
theorem ready_run {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) (top : List Bool)
    (hw : 0<w) (hqw : q≤w)
    (hb : ∀ g∈occ,(CloseoutRowsCircuitBottom.nativeWord g).length≤B)
    (hm : ∀ g∈occ,(g.gate.threshold-1).natAbs+(∑ i,(g.gate.weight i).natAbs)<2^w)
    (hqP : q≤P)
    (hi : (segment (CloseoutRowsUniversal.pool live occ) top).length≤1000*(P+2)^2) :
    ∃ (H : Fin (tapes a) → Nat) (A : Fin (tapes a) → List Bool),
      Step (readyMachine a) (budget a occ B w P)
        (Fin.addCases (PoolCold.start live occ B w top).heads (PoolCold.coldHeads a))
        (Fin.addCases (PoolCold.start live occ B w top).tapes (PoolCold.coldData a P q)) H A ∧
      H (cachePort a)=0 ∧
      A (cachePort a)=exactListWord (C10SupplierRowInput.childList a live occ) ∧
      H (domainPort a)=0 ∧ A (domainPort a)=UnaryTemplate.tape q := by
  obtain ⟨H,O,run,hcache,hcacheH,hcount,hcountH,hsource,hsourceH,htotal,htotalH,hq,hqH,_⟩ :=
    PoolCold.run a live occ B w P top hw hqw hb hm hqP hi
  let endH := dockH (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).heads (PoolCold.coldHeads a)) H
  let endA := install (PoolCold.slots a)
    (Fin.addCases (PoolCold.finish live occ B w top).tapes (PoolCold.coldData a P q)) O
  obtain ⟨r,hr,hfinal,_⟩ := DecompositionCountPosition.move_run (directions a) endH endA
  have move : Step (DecompositionCountPosition.move (directions a)) 1 endH endA
      (fun i => (directions a i).apply (endH i)) endA :=
    Step.of_run hr (by rw [hfinal]) (by rw [hfinal])
  refine ⟨(fun i => (directions a i).apply (endH i)),endA,?_,?_,?_,?_,?_⟩
  · simpa only [readyMachine,budget,show ∀ n : Nat,n+1+1=n+2 from by omega] using run.seq move
  · have hd : directions a (cachePort a) = .stay := by
      simp [directions,cache_ne_domain a]
    change (directions a (cachePort a)).apply (endH (cachePort a))=0
    rw [hd]
    change endH (cachePort a)=0
    simpa only [endH,cachePort,dockH_slot _ (PoolCold.slots_injective a)] using hcacheH
  · simpa only [endA,cachePort,install_slot _ (PoolCold.slots_injective a),
      C10SupplierRowInput.childList] using hcache
  · have hd : directions a (domainPort a) = .left := by simp [directions]
    change (directions a (domainPort a)).apply (endH (domainPort a))=0
    rw [hd]
    change endH (domainPort a)-1=0
    have he : endH (domainPort a)=1 := by
      simpa only [endH,domainPort,dockH_slot _ (PoolCold.slots_injective a)] using hqH
    rw [he]
  · simpa only [endA,domainPort,install_slot _ (PoolCold.slots_injective a)] using hq

end
end RowsConstruction.I2c.PoolReady
