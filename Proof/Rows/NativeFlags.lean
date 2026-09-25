import Proof.Rows.NativeFlagsLoop

/-! Complete native circuit-list flag stream, including the final true offset
flag. The empty family produces that flag and actual count one. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeFlagsLoop
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TrueFlagCell.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_NativeFlagsLoop.machine

def offset:=TapeEmbedding.machine 1 (TapeEmbedding.machine 3
 (TapeEmbedding.machine 1 PCJ45bee56da9f34d5a_TrueFlagCell.machine))
def machine:=Composition.machine PCJ45bee56da9f34d5a_NativeFlagsLoop.machine offset

def word {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q) :=
 output cs live x cs.length++[true]

theorem offset_run {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q N cursor : Nat)
 (source out : List Bool) :
 Step offset 1 (runHeads cursor out Q) (runBank live x B Q N source out)
  (runHeads cursor (out++[true]) (Q+1)) (runBank live x B (Q+1) N source (out++[true])) :=by
 have h:=(PCJ45bee56da9f34d5a_TrueFlagCell.run live x (B+1) (H B q (B+1)) (R B q (B+1))
  (U B q (B+1)) 0 Q (List.replicate (U B q (B+1)) false) (List.replicate (H B q (B+1)) false)
  (List.replicate (H B q (B+1)) false) out).embed
  (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate (U B q (B+1)) false)
 have h':=h.embed (![cursor,0,0] :Fin 3→Nat)
  (![source,List.replicate (U B q (B+1)) false,List.replicate (U B q (B+1)) false] :Fin 3→List Bool)
 exact h'.embed (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word N)

theorem word_length {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q) :
 (word cs live x).length=(cs.map (fun c=>c.1.length+1)).sum+1 :=by
 simp only [word,output,List.take_length,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
 congr 1
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
   simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,
    PCJ45bee56da9f34d5a_NativeCircuitFlags.flags,List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.zero_add] at ih ⊢
   omega

theorem run {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q)
 (pre tail out : List Bool) (B Q : Nat)
 (hb : ∀c∈cs,(PCJ45bee56da9f34d5a_NativeCircuitFlags.payload c.1 c.2).length≤B) :
 Step machine (budget cs.length B q+2)
  (runHeads pre.length out Q) (runBank live x B Q cs.length (pre++stream cs++tail) out)
  (runHeads (pre.length+(stream cs).length) (out++word cs live x) (Q+(word cs live x).length))
  (runBank live x B (Q+(word cs live x).length) cs.length (pre++stream cs++tail) (out++word cs live x)) :=by
 have first:=PCJ45bee56da9f34d5a_NativeFlagsLoop.run cs live x pre tail out B Q hb
 have last:=offset_run live x B (Q+(output cs live x cs.length).length) cs.length
  (pre.length+(stream cs).length) (pre++stream cs++tail) (out++output cs live x cs.length)
 have h:=first.seq last
 simpa only [machine,word,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,
  List.append_assoc,Nat.add_assoc,show 1+1=2 from rfl] using h
end
end PCJ45bee56da9f34d5a_NativeFlags
