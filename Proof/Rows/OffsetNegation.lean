import Proof.Rows.FinalNativeSignedResidue

/-! The actual binary offset is negated modulo p directly, without multiplying
by the final circuit power or serializing a native signed integer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_OffsetNegation
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey RadixSemantics
noncomputable section

def input (p w D o :Nat):Fin 6→List Bool:=
 ![frame (binary w 0),frame (binary w 0),frame (binary w p),[false],frame (binary w o),List.replicate D false]
def negated (p w D o :Nat):Fin 6→List Bool:=
 let ns:=FinalPrimeNegate.negState p w (binary w o)
 ![frame ns.1,frame ns.2.1,frame (binary w p),[ns.2.2],frame (binary w o),List.replicate D false]
def output (p w D o :Nat):Fin 6→List Bool:=
 let ns:=FinalPrimeNegate.negState p w (binary w o)
 ![frame (FinalPrimeRow.residueWord ns),frame ns.2.1,frame (binary w p),[ns.2.2],frame (binary w o),List.replicate D false]
def negate:=MaskedReset.machine FinalPrimeNegate.machine (fun _=>true)
def slots:Fin 4→Fin 6:=![0,1,3,5]
def select:=RecoveryFocus.machine slots (MaskedReset.machine FinalPrimeResidue.machine (fun _=>true))
def machine:=Composition.machine negate select

theorem run (p w D o :Nat) (hD :2*w+2≤D):
 Step machine (8*w+11) (fun _=>0) (input p w D o) (fun _=>0) (output p w D o) :=by
 let ns:=FinalPrimeNegate.negState p w (binary w o)
 have hl:=FinalPrimeNegate.negState_length p w (binary w o) (binary_length _ _)
 have neg:=(FinalPrimeNegate.negate_step p w (binary w 0) (binary w 0) (binary w o) [false]
  (binary_length _ _) (binary_length _ _) (binary_length _ _)).mask (cap:=D) (fun _=>true)
   (by intro i hi;fin_cases i <;>rfl) (by omega)
 have first:Step negate (4*w+4) (fun _=>0) (input p w D o) (fun _=>0) (negated p w D o):=by
  rw [show 4*w+4=2*(2*w+1)+2 by omega]
  refine (neg.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

 have pick:=FinalPrimeResidue.select_step ns.2.2 ns.1 ns.2.1 [ns.2.2] (hl.2.trans hl.1.symm) rfl
 rw [hl.1] at pick
 have reset:=pick.mask (cap:=D) (fun _=>true) (by intro i hi;fin_cases i <;>rfl) hD
 have ready:Step (MaskedReset.machine FinalPrimeResidue.machine (fun _=>true)) (4*w+6)
  (fun _ :Fin 4=>0) ![frame ns.1,frame ns.2.1,[ns.2.2],List.replicate D false]
  (fun _=>0) ![frame (FinalPrimeRow.residueWord ns),frame ns.2.1,[ns.2.2],List.replicate D false]:=by
  rw [show 4*w+6=2*(2*w+2)+2 by omega]
  refine (reset.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>rfl

 have docked:=ready.dock slots (by decide) (fun _ :Fin 6=>0) (negated p w D o)
  (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
 have second:Step select (4*w+6) (fun _=>0) (negated p w D o) (fun _=>0) (output p w D o):=by
  apply docked.congr
  · exact dockH_existing _ _ _ (by intro i;rfl)
  · apply HierarchyAllocation.install_eq slots (by decide)
    · intro i;fin_cases i <;>rfl
    · intro i hi;fin_cases i
      all_goals first |rfl |exact False.elim (hi 0 rfl)
 have h:=first.seq second
 simpa only [machine,show (4*w+4)+1+(4*w+6)=8*w+11 by omega] using h

theorem word_eq (p w o :Nat) (hp :0<p) (hpw :2*p≤2^w) (ho :o<p):
 FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w (binary w o))=binary w ((p-o)%p) :=by
 let ns:=FinalPrimeNegate.negState p w (binary w o)
 have hl:=FinalPrimeNegate.negState_length p w (binary w o) (binary_length _ _)
 have hlen:(FinalPrimeRow.residueWord ns).length=w:=by
  unfold FinalPrimeRow.residueWord
  split
  · exact hl.2
  · exact hl.1
 have hv:value (FinalPrimeRow.residueWord ns)=(p-o)%p:=by
  rw [←FinalPrimeRow.residueOf_word]
  change FinalPrimeRow.residueOf (FinalPrimeNegate.negState p w (binary w o))=_
  rw [FinalPrimeNegate.negate_residue p w _ (binary_length _ _) hp hpw
   (by rw [binary_value w o (by omega)];exact ho),binary_value w o (by omega)]
 have h:=BoundedCounter.binary_of_value (FinalPrimeRow.residueWord ns)
 rw [hlen,hv] at h
 exact h.symm

theorem output_lengths (p w D o :Nat) (i :Fin 5):
 (output p w D o (i.castAdd 1)).length≤2*w+1 :=by
 have hl:=FinalPrimeNegate.negState_length p w (binary w o) (binary_length _ _)
 have hr:(FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w (binary w o))).length=w:=by
  unfold FinalPrimeRow.residueWord
  split
  · exact hl.2
  · exact hl.1
 fin_cases i
 · change (frame (FinalPrimeRow.residueWord (FinalPrimeNegate.negState p w (binary w o)))).length≤_
   rw [frame_length,hr]
 · change (frame (FinalPrimeNegate.negState p w (binary w o)).2.1).length≤_
   rw [frame_length,hl.2]
 · change (frame (binary w p)).length≤_
   rw [frame_length,binary_length]
 · change 1≤2*w+1;omega
 · change (frame (binary w o)).length≤_
   rw [frame_length,binary_length]

end
end PCJ45bee56da9f34d5a_OffsetNegation
