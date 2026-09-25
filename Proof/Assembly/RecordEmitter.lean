import Proof.CaseAnalysis.FinalSingleAppend
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9856d3e73b1d4df0_.RecordEmitter
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RecoveryRootRound CloseoutRowsEstimatorCoefficients
open CompetitorRawFieldEmit
noncomputable section

def fields (b : Nat) (e : Stream.Entry) : Fin 10 → List Bool :=
 Fin.addCases (m:=6) (n:=4) (motive:=fun _=>List Bool) (Stream.recordFields b e.coefficient e.count e.denominator) (fun _ : Fin 4 => [])
def order : List (Fin 10) := [0,1,2,3,4,5]
def base (b : Nat) (e : Stream.Entry) (D cap : Nat) (payload : List Bool) : Fin 10 → List Bool :=
 Fin.addCases (m:=6) (n:=4) (motive:=fun _=>List Bool) (fun i : Fin 6 => frame (Stream.recordFields b e.coefficient e.count e.denominator i))
   (![payload,List.replicate cap false,List.replicate D true,List.replicate (D+1) false] : Fin 4 → List Bool)
def emitCost (b : Nat) := 40*b+56
def bank (b : Nat) (e : Stream.Entry) (D cap : Nat) (payload : List Bool) : Fin 11 → List Bool :=
 Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool) (base b e D cap payload) (fun _ : Fin 1 => List.replicate (emitCost b) false)
def raw := listProgram (6 : Fin 10) 7 order
def emit := MaskedReset.machine raw (fun _ => true)
def eraseSlots : Fin 3 → Fin 11 := ![6,8,9]
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
def machine := Composition.machine erase emit

theorem stream_eq (b : Nat) (e : Stream.Entry) :
 stream (fields b e) order = Stream.entryWord b e := by rfl

theorem cost_eq (b : Nat) (e : Stream.Entry) : listCost (fields b e) order=emitCost b := by
 simp [Fin.addCases,listCost,fields,order,Stream.recordFields,CompetitorRationalDecision.width,
   SignedSortKey.binary_length,emitCost]
 omega

theorem raw_run (b : Nat) (e : Stream.Entry) (D cap : Nat) (hc : 4*b+5≤cap) :
 Step raw (emitCost b) (fun _=>0) (base b e D cap [])
   (Function.update (fun _=>0) 6 (Stream.entryWord b e).length)
   (base b e D cap (Stream.entryWord b e)) := by
 obtain ⟨r,hr,hh,ht,hs⟩ := list_run (6 : Fin 10) 7 order (fields b e)
   (by decide) (by simp [order]) (by simp [order]) [] cap (fun _=>0) (base b e D cap [])
   (by simp) rfl rfl (by intro j hj; simp [order] at hj; rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
   rfl rfl (by
     intro j hj
     simp [order] at hj
     rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;>
       simp [Fin.addCases,fields,Stream.recordFields,CompetitorRationalDecision.width] <;> omega)
 rw [cost_eq] at hr hs
 refine ⟨r,hr,?_,?_,hs.le⟩
 · simpa only [List.nil_append,stream_eq] using hh
 · rw [ht,List.nil_append,stream_eq]
   funext i
   fin_cases i <;> simp [Fin.addCases,base,Function.update_apply]

theorem padded_emit (b : Nat) (e : Stream.Entry) (D cap : Nat) (hc : 4*b+5≤cap) :
 Step emit (2*emitCost b+2) (fun _=>0) (bank b e D cap (List.replicate D false))
   (fun _=>0) (bank b e D cap (ZeroPadding.pad D (Stream.entryWord b e))) := by
 let pads : Fin 10 → Nat := fun i => if i=6 then D else 0
 have h := (raw_run b e D cap hc).pad pads
 have h' := h.mask (fun _=>true) (by intros;rfl) (le_refl (emitCost b))
 refine (h'.congr_in (by funext i;fin_cases i <;> rfl) ?_).congr (by funext i;fin_cases i <;> rfl) ?_
 · funext i
   fin_cases i <;> simp [bank,base,pads,ZeroPadding.pad,Fin.addCases]
 · funext i
   fin_cases i <;> simp [bank,base,pads,ZeroPadding.pad,Fin.addCases]

/-- Reusable payload writing: old contents are bounded, erased into their
allocated backing, then replaced. No clearing to an impossible empty tape. -/
theorem run (b : Nat) (e : Stream.Entry) (D cap : Nat) (old : List Bool)
 (hc : 4*b+5≤cap) (hold : old.length≤D) :
 Step machine (2*D+4+1+(2*emitCost b+2)) (fun _=>0) (bank b e D cap old)
   (fun _=>0) (bank b e D cap (ZeroPadding.pad D (Stream.entryWord b e))) := by
 have h := (Step.of_ready (RecoveryScratchErase.erase_ready D (D+1)
   (fun _ : Fin 1 => old) (by intro i;exact hold))).dock eraseSlots (by decide)
   (fun _=>0) (bank b e D cap old) (by intro i;rfl)
   (by intro i;fin_cases i <;> rfl)
 have he : Step erase (2*D+4) (fun _=>0) (bank b e D cap old)
   (fun _=>0) (bank b e D cap (List.replicate D false)) := by
   refine h.congr ?_ ?_
   · exact dockH_existing eraseSlots (fun _=>0) (fun _=>0) (by intro j;rfl)
   · funext i
     by_cases hi : ∃ j,eraseSlots j=i
     · obtain ⟨j,rfl⟩ := hi
       rw [install_slot _ (by decide : Function.Injective eraseSlots)]
       fin_cases j <;> simp [Fin.addCases,bank,base,eraseSlots]
     · rw [install_other _ _ _ _ (by intro j hj;exact hi ⟨j,hj⟩)]
       have h6 : i≠6 := fun h=>hi ⟨0,h.symm⟩
       fin_cases i <;> simp [Fin.addCases,bank,base] at h6 ⊢
 exact he.seq (padded_emit b e D cap hc)


/-- The literal encoder consumer, at actual ambient cursors. Other cells and
heads are retained; field/source production is not assumed to be free. -/
theorem docked_run {B : Nat} (slots : Fin 11 → Fin B) (inj : Function.Injective slots)
 (b : Nat) (e : Stream.Entry) (D cap : Nat) (old : List Bool)
 (hc : 4*b+5≤cap) (hold : old.length≤D)
 (H : Fin B → Nat) (A : Fin B → List Bool)
 (hH : ∀ i,H (slots i)=0) (hA : ∀ i,A (slots i)=bank b e D cap old i) :
 let out := bank b e D cap (ZeroPadding.pad D (Stream.entryWord b e))
 Step (RecoveryFocus.machine slots machine) (2*D+4+1+(2*emitCost b+2)) H A H (install slots A out) ∧
 install slots A out (slots 6)=ZeroPadding.pad D (Stream.entryWord b e) ∧
 (∀ i,(∀ j,slots j≠i) → install slots A out i=A i) := by
 dsimp only
 refine ⟨((run b e D cap old hc hold).dock slots inj H A hH hA).congr
   (dockH_existing slots H _ hH) rfl,?_,?_⟩
 · rw [install_slot _ inj];rfl
 · exact fun i hi=>install_other slots A _ i hi

/-- Exact composition with the existing append consumer. Its remaining tape
matches are explicit, and the native record and complete costs stay shared. -/
theorem append_run {B : Nat} (enc : Fin 11 → Fin B) (ei : Function.Injective enc)
 (app : Fin 6 → Fin B) (ai : Function.Injective app)
 (b : Nat) (e : Stream.Entry) (D cap logSize resetSize : Nat) (old : List Bool)
 (xs : List Stream.Entry) (hc : 4*b+5≤cap) (hold : old.length≤D)
 (H : Fin B → Nat) (A : Fin B → List Bool)
 (hH : ∀ i,H (enc i)=0) (hA : ∀ i,A (enc i)=bank b e D cap old i)
 (haH : ∀ i,H (app i)=0)
 (haA : ∀ i,install enc A (bank b e D cap (ZeroPadding.pad D (Stream.entryWord b e))) (app i)=
   CloseoutFinalC10AppendPositioning.tapes b D logSize resetSize e xs i)
 (hl : 20*b+27≤logSize) (hr : CloseoutFinalC10AppendPositioning.rawBudget b xs.length≤resetSize) :
 let mid := install enc A (bank b e D cap (ZeroPadding.pad D (Stream.entryWord b e)))
 Step (Composition.machine (RecoveryFocus.machine enc machine)
   (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
   (2*D+4+1+(2*emitCost b+2)+1+CloseoutFinalC10AppendPositioning.budget b xs.length) H A H
   (install app mid (CloseoutFinalC10AppendPositioning.tapes b D logSize resetSize e (xs++[e]))) := by
 exact (docked_run enc ei b e D cap old hc hold H A hH hA).1.seq
   (CloseoutFinalC10SingleAppend.docked_run app ai b D logSize resetSize e xs H _ haH haA hl hr).1

end
end PCJ9856d3e73b1d4df0_.RecordEmitter
