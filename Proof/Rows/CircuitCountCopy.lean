import Proof.Rows.TopArity

/-! Skip exactly four native headers and physically copy only the fifth field.
The original target is never decoded as unary. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CircuitCountCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open StablePartition.Workspace
noncomputable section

def heads (pos len : Nat):Fin 3→Nat:=![pos,0,len]
def tapes (source scratch out : List Bool):Fin 3→List Bool:=![source,scratch,out]
def scratch (n : Nat) (backing : List Bool):=overlay (UnaryTemplate.tape (natBitLength n)) backing

theorem field_run (keep : Bool) (pre tail backing out : List Bool) (n : Nat):
    Step (PCPPQueryField.machine keep) (2*natBitLength n+3) (heads pre.length out.length)
      (tapes (pre++natWord n++tail) backing out)
      (heads (pre.length+(natWord n).length) (out++PCPPQueryField.selected keep (natWord n)).length)
      (tapes (pre++natWord n++tail) (scratch n backing) (out++PCPPQueryField.selected keep (natWord n))):=by
  obtain ⟨r,hr,hf,_⟩:=PCPPQueryField.nat_run keep pre tail backing out n
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  simpa only [PCPPQueryField.cfg,PCPPQueryField.payload,heads,tapes,scratch,
    DecompositionSource.natWord_length,Nat.add_assoc] using h

def source (tag q L target N : Nat) (tail : List Bool):=
  natWord tag++natWord q++natWord L++natWord target++natWord N++tail
def header (tag q L target : Nat):=natWord tag++natWord q++natWord L++natWord target
def after (tag q L target N : Nat) (backing : List Bool):=
  scratch N (scratch target (scratch L (scratch q (scratch tag backing))))
def budget (tag q L target N : Nat):=
  2*(natBitLength tag+natBitLength q+natBitLength L+natBitLength target+natBitLength N)+19
def skip:=PCPPQueryField.machine false
def keep:=PCPPQueryField.machine true
def machine:=Composition.machine (Composition.machine (Composition.machine (Composition.machine skip skip) skip) skip) keep

theorem run (tag q L target N : Nat) (tail backing : List Bool):
    Step machine (budget tag q L target N) (heads 0 0)
      (tapes (source tag q L target N tail) backing [])
      (heads ((header tag q L target).length+(natWord N).length) (natWord N).length)
      (tapes (source tag q L target N tail) (after tag q L target N backing) (natWord N)):=by
  have h1:=field_run false [] (natWord q++natWord L++natWord target++natWord N++tail) backing [] tag
  have h2:=field_run false (natWord tag) (natWord L++natWord target++natWord N++tail) (scratch tag backing) [] q
  have h3:=field_run false (natWord tag++natWord q) (natWord target++natWord N++tail) (scratch q (scratch tag backing)) [] L
  have h4:=field_run false (natWord tag++natWord q++natWord L) (natWord N++tail)
    (scratch L (scratch q (scratch tag backing))) [] target
  have h5:=field_run true (header tag q L target) tail
    (scratch target (scratch L (scratch q (scratch tag backing)))) [] N
  simp only [PCPPQueryField.selected,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,
    List.length_nil,Nat.zero_add,List.length_append,List.append_assoc,Nat.add_assoc] at h1 h2 h3 h4
  simp only [PCPPQueryField.selected,if_true,List.nil_append,header,List.length_append,List.append_assoc,Nat.add_assoc] at h5
  have all:=(((h1.seq h2).seq h3).seq h4).seq h5
  unfold machine skip keep
  convert all using 1 <;>first | rfl | (unfold budget;omega) | simp [source,header,after,List.length_append,List.append_assoc,Nat.add_assoc]
end
end PCJ45bee56da9f34d5a_CircuitCountCopy
