import Proof.CaseAnalysis.RowsModeCacheReuseBounds

/-! Repeated cache passes retain original inputs and the last child count.
Private backing is erased at the next entry, before the actual source runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reuseCaps (D : Nat) : Fin 25→Nat:=
  ![0,D,0,0,D,0,D,D,D,0,D,0,0,D,D,D,D,D,D,D,0,0,D,D,0]
def reuseHeads (out : List Bool) : Fin 28→Nat:=fun i=>if i=20 then out.length else 0
def reuseData (p : Parameters) (M R D : Nat) (out : List Bool) (A : Fin 15→List Bool) : Fin 28→List Bool:=
  ![List.replicate p.rank true,A 0,p.lower,p.upper,A 1,p.translation,A 2,A 3,A 4,
    CompareMachine.word p.rank,A 5,p.mask,List.replicate p.level true,A 6,A 7,A 8,A 9,A 10,
    A 11,A 12,out,List.replicate p.C true,A 13,A 14,CompareMachine.word M,
    List.replicate R false,List.replicate D true,List.replicate (D+1) false]
def reuseEraseSlots : Fin 17→Fin 28:=![1,4,6,7,8,10,13,14,15,16,17,18,19,22,23,26,27]
def reuseFinal (mode : Fin 3) (p : Parameters) (M D : Nat) : Fin 15→List Bool:=fun i=>
  ZeroPadding.pad D (loopData p (atState mode p (initialState []) M []) M (privateSlots i))

theorem reuse_initial (p : Parameters) (M D : Nat) (out : List Bool)
    (hC : p.C+1 ≤ D) (hr : p.rank+1 ≤ D) (hD : 3 ≤ D) :
    (fun i=>ZeroPadding.pad (reuseCaps D i) (initData p M out 0 i))=
      (fun i=>reuseData p M 0 D out (fun _=>List.replicate D false) (i.castAdd 3)):=by
  have hz (n : Nat) (hn : n ≤ D) : ZeroPadding.pad D (List.replicate n false)=List.replicate D false:=by
    simpa only [max_eq_left hn] using Rewind.Workspace.pad_zeros D n
  have h1:=hz 1 (by omega)
  have h3:=hz 3 hD
  simp only [List.replicate_succ,List.replicate_zero] at h1 h3
  funext i;fin_cases i <;>
    simp [reuseCaps,reuseData,initData,loopData,data,fields,CloseoutRowsModeHashFields.before,
      extras,initialState,label,Fin.addCases,EquationZeroField.binary_zero,CompareMachine.word,
      ZeroPadding.pad_zero,hz p.C (by omega),hz (p.C+1) hC,hz (p.rank+1) hr,h1,h3]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
