import Proof.Rows.CircuitFlagRun

/-! The physical flag callback consumes exactly Production's native circuit
codec. All count and individual-gate width bounds follow from its byte cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
namespace PCJ45bee56da9f34d5a_NativeCircuitCodec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.CompilerSemantics
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
open PCJ45bee56da9f34d5a_NativeGateLoop (word stream)
open PCJ45bee56da9f34d5a_FramedGateBank (strict)
noncomputable section

def thrGates {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=
 List.ofFn (fun i=> (c.bottom (retainedTopIndex c i)).gate)
def thrTop {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :=thresholdWord (nonStrictAsStrict (retainedTopGate c))

theorem native_gate {q : Nat} (g : SupportedNormalizedGate q) :
 frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g)=word g.gate :=by
 simp only [PCJd4d1d9d7d1fa4313_Production.bottomWord,thresholdWord,nonStrictAsStrict,word,
  PoolEntryLoad.word,strict,exactWord,List.append_assoc]

theorem thrWord_eq {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :
 PCJd4d1d9d7d1fa4313_Production.thrWord c=payload (thrGates c) (thrTop c) :=by
 simp only [PCJd4d1d9d7d1fa4313_Production.thrWord,payload,thrGates,thrTop,List.length_ofFn,stream]
 have hm : (List.ofFn (fun i=>c.bottom (retainedTopIndex c i))).map (fun g=>g.gate)=
   List.ofFn (fun i=>(c.bottom (retainedTopIndex c i)).gate):=by rw [List.map_ofFn];rfl
 rw [←hm,List.flatMap_map]
 congr 1
 apply List.flatMap_congr
 intro g _
 exact native_gate g

theorem count_le_stream {q : Nat} (gs : List (NormalizedThresholdGate q)) :gs.length≤(stream gs).length :=by
 induction gs with
 | nil=>simp [stream]
 | cons g gs ih=>
   have hg : 1≤(word g).length:=by rw [word,frame_length];omega
   simp only [stream,List.flatMap_cons,List.length_cons,List.length_append] at ih ⊢
   omega

theorem gate_le_stream {q : Nat} (gs : List (NormalizedThresholdGate q)) (g : NormalizedThresholdGate q) (hg : g∈gs) :
 (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤(stream gs).length :=by
 induction gs with
 | nil=>simp at hg
 | cons a gs ih=>
   simp only [List.mem_cons] at hg
   simp only [stream,List.flatMap_cons,List.length_append]
   rcases hg with rfl|hg
   · have h : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤(word g).length:=by
       simp only [word,frame_length,PoolEntryLoad.word,List.length_append,strict,exactWord,
         PCJ45bee56da9f34d5a_FullGateBounds.source]
       omega
     omega
   · have h:=ih hg;unfold stream at h;omega

theorem bounds {q : Nat} (gs : List (NormalizedThresholdGate q)) (top : List Bool) (B : Nat)
 (hp : (payload gs top).length≤B) :gs.length≤B ∧
  (∀g∈gs,(PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) ∧ top.length≤B :=by
 have hn:=count_le_stream gs
 simp only [payload,List.length_append,frame_length] at hp
 refine ⟨by omega,?_,by omega⟩
 intro g hg
 have h:=gate_le_stream gs g hg
 omega
end
end PCJ45bee56da9f34d5a_NativeCircuitCodec
