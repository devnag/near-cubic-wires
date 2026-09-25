import Proof.Rows.NativeFamilyCount
import Proof.Rows.NativeFlagsMeaning

/-! Complete original native family traversal. Its loop driver is produced
from the fifth physical header; all size premises follow from the native byte cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFamilyFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds PCJ45bee56da9f34d5a_NativeFamilyCount
open PCJ45bee56da9f34d5a_NativeFlagsLoop (Circuit stream)
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeFamilyCount.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeFlags.machine

def machine:=Composition.machine PCJ45bee56da9f34d5a_NativeFamilyCount.machine PCJ45bee56da9f34d5a_NativeFlags.machine
def caps (U : Nat):Fin 128→Nat:=Fin.addCases (m:=127) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>U)
def source {q : Nat} (tag L target : Nat) (cs : List (Circuit q)) :=
 PCJ45bee56da9f34d5a_CircuitCountCopy.source tag q L target cs.length (stream cs)
def budget (tag q L target N B : Nat):=
 PCJ45bee56da9f34d5a_CircuitCountAdvance.budget tag q L target N (U B q (B+1))+
 PCJ45bee56da9f34d5a_NativeFlagsLoop.budget N B q+3

theorem pad_last (a :Fin 127→List Bool) (count : List Bool) (U : Nat) :
 (fun i=>ZeroPadding.pad (caps U i) (Fin.addCases (m:=127) (n:=1) (motive:=fun _=>List Bool) a (fun _=>count) i))=
 Fin.addCases (m:=127) (n:=1) (motive:=fun _=>List Bool) a (fun _=>ZeroPadding.pad U count) :=by
 funext i
 refine Fin.addCases (m:=127) (n:=1) (fun _=>?_) (fun _=>?_) i
 · simp only [caps,Fin.addCases_left,ZeroPadding.pad_zero]
 · simp only [caps,Fin.addCases_right]

theorem count_le_stream {q : Nat} (cs : List (Circuit q)) :cs.length≤(stream cs).length :=by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
   have hc : 1≤(PCJ45bee56da9f34d5a_NativeFlagsLoop.word c).length:=by
    rw [PCJ45bee56da9f34d5a_NativeFlagsLoop.word,frame_length];omega
   simp only [stream,List.flatMap_cons,List.length_cons,List.length_append] at ih ⊢
   omega

theorem payload_le_stream {q : Nat} (cs : List (Circuit q)) (c : Circuit q) (hc : c∈cs) :
 (payload c.1 c.2).length≤(stream cs).length :=by
 induction cs with
 | nil=>simp at hc
 | cons a cs ih=>
   simp only [List.mem_cons] at hc
   simp only [stream,List.flatMap_cons,List.length_append]
   rcases hc with rfl|hc
   · have h : (payload c.1 c.2).length≤(PCJ45bee56da9f34d5a_NativeFlagsLoop.word c).length:=by
      rw [PCJ45bee56da9f34d5a_NativeFlagsLoop.word,frame_length];omega
     omega
   · have h:=ih hc;unfold stream at h;omega

theorem fits {q : Nat} (tag L target B : Nat) (cs : List (Circuit q)) (hb : (source tag L target cs).length≤B) :
 (∀c∈cs,(payload c.1 c.2).length≤B) ∧
 PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target cs.length+2≤U B q (B+1) ∧
 PCPPQueryNatural.budget cs.length<U B q (B+1) :=by
 have hs:(stream cs).length≤B:=by
  simp only [source,PCJ45bee56da9f34d5a_CircuitCountCopy.source,List.length_append] at hb;omega
 have hn:cs.length≤B:=(count_le_stream cs).trans hs
 refine ⟨fun c hc=>(payload_le_stream cs c hc).trans hs,?_,PCJ45bee56da9f34d5a_NativeCircuitFlags.count_fits cs.length B q hn⟩
 have hp:B+q+(B+1)+1≤(B+q+(B+1)+1)^2:=Nat.le_self_pow (by decide) _
 have hpos:1≤(B+q+(B+1)+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [source,PCJ45bee56da9f34d5a_CircuitCountCopy.source,List.length_append,DecompositionSource.natWord_length] at hb
 unfold PCJ45bee56da9f34d5a_CircuitCountCopy.budget U PCJ45bee56da9f34d5a_FullGateCapacity.capacity
 omega

theorem run {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (out : List Bool) (B Q tag L target : Nat) (hb : (source tag L target cs).length≤B) :
 Step machine (budget tag q L target cs.length B)
  (heads 0 out Q 0) (bank live x B Q (source tag L target cs) out (List.replicate (U B q (B+1)) false))
  (heads (source tag L target cs).length (out++PCJ45bee56da9f34d5a_NativeFlags.word cs live x)
    (Q+(PCJ45bee56da9f34d5a_NativeFlags.word cs live x).length) 1)
  (bank live x B (Q+(PCJ45bee56da9f34d5a_NativeFlags.word cs live x).length) (source tag L target cs)
    (out++PCJ45bee56da9f34d5a_NativeFlags.word cs live x) (ZeroPadding.pad (U B q (B+1)) (CompareMachine.word cs.length))) :=by
 obtain ⟨hp,hc,hn⟩:=fits tag L target B cs hb
 have first:=PCJ45bee56da9f34d5a_NativeFamilyCount.run live x B Q tag L target cs.length (stream cs) out hc hn
 have last:=(PCJ45bee56da9f34d5a_NativeFlags.run cs live x
  (PCJ45bee56da9f34d5a_CircuitCountCopy.header tag q L target++natWord cs.length) [] out B Q hp).pad (caps (U B q (B+1)))
 unfold PCJ45bee56da9f34d5a_NativeFlagsLoop.runBank at last
 rw [pad_last,pad_last] at last
 simp only [PCJ45bee56da9f34d5a_CircuitCountCopy.source,PCJ45bee56da9f34d5a_CircuitCountCopy.header,
  List.length_append,List.append_assoc,List.append_nil,Nat.add_assoc] at first last
 have h:=first.seq last
 have hf : PCJ45bee56da9f34d5a_CircuitCountAdvance.budget tag q L target cs.length (U B q (B+1))+1+
  (PCJ45bee56da9f34d5a_NativeFlagsLoop.budget cs.length B q+2)=budget tag q L target cs.length B :=by unfold budget;omega
 simpa only [machine,hf,source,PCJ45bee56da9f34d5a_CircuitCountCopy.source,List.length_append,
  List.append_assoc,Nat.add_assoc,PCJ45bee56da9f34d5a_NativeFlagsLoop.runHeads,heads,bank] using h
end
end PCJ45bee56da9f34d5a_NativeFamilyFlags
