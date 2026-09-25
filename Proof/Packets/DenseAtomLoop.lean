import Proof.Packets.DenseAtomIteration

/-! The physically counted complete dense-table pass; no per-iteration
execution premise appears in the final run theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomProgram
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)

noncomputable def machine := RepeatMachine.machine NativeIndexedAtom.machine (fun _ _=>true)
def budget (C R count : Nat) := count*(bodyBudget C R+3)+3

theorem run (C R tag : Nat) (cs : List Pair) (initial : List Packet)
    (hR : C+2≤R) (hcount : cs.length≤C) (hcodes : ∀i<cs.length,Nat.pair tag i<C)
    (hcache : (cacheWord cs).length≤R) (hinit : initial.length=C)
    (hinits : ∀P∈initial,PacketVector.Fits R P)
    (hcopy : ∀p∈cs,CloseoutRowsRawPairCopy.budget p≤R+3)
    (hfits : ∀p∈cs,∀m∈p.1++p.2,∀i∈m,i<C)
    (hdata : ∀p∈cs,∀i,(NativeNormalized.A C (p.1++p.2) [] i).length≤R)
    (hfuel : ∀p∈cs,NativeNormalized.budget C (p.1++p.2)+3≤R) :
    Step machine (budget C R cs.length)
      (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>Nat) (H tag cs 0) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool) (A C R tag cs initial 0)
        (fun _ : Fin 1=>CompareMachine.word cs.length))
      (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>Nat) (H tag cs cs.length) (fun _ : Fin 1=>1))
      (Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool) (A C R tag cs initial cs.length)
        (fun _ : Fin 1=>CompareMachine.word cs.length)) := by
  exact PhysicalRepeatStep.run NativeIndexedAtom.machine cs.length (bodyBudget C R)
    (H tag cs) (A C R tag cs initial)
    (fun j hj=>iteration_run C R tag cs initial hR hcount hcodes hcache hinit hinits hcopy hfits hdata hfuel j hj)

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomProgram
