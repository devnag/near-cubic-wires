import Proof.Rows.NativeScaleWeights

/-! A selected native child is physically mapped to scaled residues in native
weight order, followed by its negative target. The count driver is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleEquation
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def weights {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)):=List.ofFn eq.weights
def source {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)):=PCJ45bee56da9f34d5a_NativeScaleWeights.stream (weights eq)++intWord eq.target
def result (a p w : Nat) {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)):=
  FinalPrimeModular.blocks (PCJ45bee56da9f34d5a_NativeScaleWeights.words a p w (weights eq)) 0 n++
    frame (binary w ((a*FinalPrimeReduce.intResidue p (-eq.target))%p))
def machine:=Composition.machine PCJ45bee56da9f34d5a_NativeScaleWeights.machine (TapeEmbedding.machine 1 (PCJ45bee56da9f34d5a_NativeScaleRun.machine true))
def budget (n F w U : Nat) (target : Int):=PCJ45bee56da9f34d5a_NativeScaleWeights.budget n F w U+1+PCJ45bee56da9f34d5a_NativeScaleRun.budget true target w F U
def heads (pos len : Nat):Fin 92→Nat:=Fin.addCases (m:=91) (n:=1)
  (motive:=fun _=>Nat) (PCJ45bee56da9f34d5a_NativeScaleInput.heads pos len 0) (fun _=>1)
def bank (N a p w F U : Nat) (bits out : List Bool):Fin 92→List Bool:=
  Fin.addCases (m:=91) (n:=1) (motive:=fun _=>List Bool)
    (PCJ45bee56da9f34d5a_NativeScaleInput.bank a p w F U bits out (List.replicate U false)) (fun _=>CompareMachine.word N)

theorem run (pre tail out : List Bool) (a p w F U : Nat) {n : Nat}
    (eq : SupplierPipeline.LabelledEquation (Fin n)) (hp : 0<p) (hpw : 2*p≤2^w) (ha : a<2^w)
    (hweights : ∀i : Fin n,C10NativeResidueCallback.coreBudget false (eq.weights i) w+1≤F)
    (htarget : C10NativeResidueCallback.coreBudget true eq.target w+1≤F)
    (hU : 1024*(w+1)^2+2≤U) :
    Step machine (budget n F w U eq.target) (heads pre.length out.length)
      (bank n a p w F U (pre++source eq++tail) out)
      (heads (pre.length+(source eq).length) (out.length+(n+1)*(2*w+1)))
      (bank n a p w F U (pre++source eq++tail) (out++result a p w eq)):=by
  let before:=pre++PCJ45bee56da9f34d5a_NativeScaleWeights.stream (weights eq)
  let acc:=out++FinalPrimeModular.blocks (PCJ45bee56da9f34d5a_NativeScaleWeights.words a p w (weights eq)) 0 n
  have first:=PCJ45bee56da9f34d5a_NativeScaleWeights.run pre (intWord eq.target++tail) (weights eq) out a p w F U hp hpw ha (by
    intro z hz;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hz;exact hweights i) hU
  simp only [weights,List.length_ofFn] at first
  have first':Step PCJ45bee56da9f34d5a_NativeScaleWeights.machine (PCJ45bee56da9f34d5a_NativeScaleWeights.budget n F w U) (heads pre.length out.length)
      (bank n a p w F U (pre++source eq++tail) out)
      (heads before.length (out.length+n*(2*w+1)))
      (bank n a p w F U (pre++source eq++tail) acc):=by
    simpa only [heads,bank,source,before,List.length_append,acc,weights,List.append_assoc] using first
  have target:=(PCJ45bee56da9f34d5a_NativeScaleRun.run true before tail acc eq.target a p w F U hp hpw ha htarget hU).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>CompareMachine.word n)
  have count:=FinalPrimeModular.blocks_length (PCJ45bee56da9f34d5a_NativeScaleWeights.words a p w (weights eq)) w
    (fun _=>binary_length _ _) 0 n
  have last:Step (TapeEmbedding.machine 1 (PCJ45bee56da9f34d5a_NativeScaleRun.machine true)) (PCJ45bee56da9f34d5a_NativeScaleRun.budget true eq.target w F U)
      (heads before.length (out.length+n*(2*w+1)))
      (bank n a p w F U (pre++source eq++tail) acc)
      (heads (pre.length+(source eq).length) (out.length+(n+1)*(2*w+1)))
      (bank n a p w F U (pre++source eq++tail) (out++result a p w eq)):=by
    simpa only [heads,bank,before,source,List.append_assoc,acc,List.length_append,count,
      result,↓reduceIte,frame_length,binary_length,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using target
  exact first'.seq last

theorem result_flatMap (a p w : Nat) {n : Nat} (eq : SupplierPipeline.LabelledEquation (Fin n)) :
    result a p w eq=(weights eq++[-eq.target]).flatMap
      (fun z=>frame (binary w ((a*FinalPrimeReduce.intResidue p z)%p))):=by
  unfold result
  have h:=PCJ45bee56da9f34d5a_NativeScaleWeights.concatenated a p w (weights eq)
  simp only [weights,List.length_ofFn] at h
  simpa only [weights,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using congrArg
    (fun xs=>xs++frame (binary w ((a*FinalPrimeReduce.intResidue p (-eq.target))%p))) h

end
end PCJ45bee56da9f34d5a_NativeScaleEquation
