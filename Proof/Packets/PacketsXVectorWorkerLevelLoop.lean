import Proof.Packets.PacketsXVectorWorkerTransfer
import Proof.Packets.PacketsXVectorWorkerChildNat
import Proof.Packets.PhysicalIndexedExists
import Proof.Packets.PhysicalAppendUpdate

/-! Full299-tape descending level execution with an exact resident vector
invariant. Level bodies are the concrete preparation, parent loop, and paid
bank-turnover program; the only abstract parameters are finite provider
machines whose actual run lemmas instantiate the compositional premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def levelData (C R N ci pi li : Nat) (left right : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) : Fin 298→List Bool :=
  Fin.addCases (m:=296) (n:=2) (motive:=fun _=>List Bool)
    (A C R ci pi li left right [] previous next fields extra) (fun _=>ZeroPadding.pad R (CompareMachine.word N))

theorem update_level_index (C R ci pi li li' : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    Function.update (A C R ci pi li left right acc previous next fields extra) 260
      (ZeroPadding.pad R (CompareMachine.word li'))=A C R ci pi li' left right acc previous next fields extra := by
  funext i
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · have hn:(k.castAdd 8).castAdd 32≠(260 : Fin 296) := by
        intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
      rw [Function.update_of_ne hn]
      simp only [A,VectorController.A,Fin.addCases_left]
    · fin_cases k <;>rfl
  · have hn:j.natAdd 264≠(260 : Fin 296) := by
      intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    rw [Function.update_of_ne hn]
    simp only [A,Fin.addCases_right]

theorem update_levelData (C R N ci pi li li' : Nat) (left right : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) :
    Function.update (levelData C R N ci pi li left right previous next fields extra) 260
      (ZeroPadding.pad R (CompareMachine.word li'))=levelData C R N ci pi li' left right previous next fields extra := by
  change Function.update (Fin.addCases (m:=296) (n:=2) (motive:=fun _=>List Bool) _ _) ((260 : Fin 296).castAdd 2) _=_
  rw [PhysicalAppendUpdate.left,update_level_index]
  rfl

def LevelReady (C R N depth : Nat) (table : Nat→List (Ring.Poly Nat))
    (Q : Nat→List (List Bool)→List (List Bool)→(Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (done : Nat) (t : Fin 298→List Bool) : Prop :=
  ∃ci pi left right fields extra,ci+1≤R ∧ pi+1≤R ∧ Q done left right fields extra ∧
    t=levelData C R N ci pi (depth-done) left right (vectorBank C R (table done))
      (PacketVector.bank R (List.replicate N [])) fields extra

attribute [local irreducible] levelBody machine

theorem level_loop_run {s l : Nat} (provider : Machine 256 s) (levelProvider : Machine 256 l)
    (C R N depth E : Nat) (table : Nat→List (Ring.Poly Nat))
    (Q : Nat→List (List Bool)→List (List Bool)→(Fin 222→List Bool)→(Fin 32→List Bool)→Prop)
    (input : Fin 298→List Bool) (hinput : LevelReady C R N depth table Q 0 input)
    (hdepth : depth+1≤R) (hN : N+1≤R)
    (level_run : ∀done,done<depth→∀ci pi left right fields extra,
      ci+1≤R→pi+1≤R→Q done left right fields extra→
      ∃left' right' fields' extra',Step (levelBody provider levelProvider) E (levelH (fun _=>0))
        (levelData C R N ci pi (depth-(done+1)) left right (vectorBank C R (table done))
          (PacketVector.bank R (List.replicate N [])) fields extra)
        (levelH (fun _=>0))
        (levelData C R N N N (depth-(done+1)) left' right' (vectorBank C R (table (done+1)))
          (PacketVector.bank R (List.replicate N [])) fields' extra') ∧ Q (done+1) left' right' fields' extra') :
    ∃output,Step (machine provider levelProvider) (depth*(E+2*depth+6)+3)
      (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases input (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word depth)))
      (Fin.addCases (levelH (fun _ : Fin 222=>0)) (fun _ : Fin 1=>1))
      (Fin.addCases output (fun _ : Fin 1=>ZeroPadding.pad R (CompareMachine.word depth))) ∧
      LevelReady C R N depth table Q depth output := by
  have step (done : Nat) (hd : done<depth) (t : Fin 298→List Bool)
      (ht : LevelReady C R N depth table Q done t) :
      ∃b,Step (levelBody provider levelProvider) E (levelH (fun _=>0))
        (Function.update t 260 (ZeroPadding.pad R (CompareMachine.word (depth-(done+1))))) (levelH (fun _=>0)) b ∧
        LevelReady C R N depth table Q (done+1) b := by
    obtain ⟨ci,pi,left,right,fields,extra,hci,hpi,hq,rfl⟩:=ht
    rw [update_levelData]
    obtain ⟨left',right',fields',extra',run,hq'⟩:=level_run done hd ci pi left right fields extra hci hpi hq
    exact ⟨_,run,N,N,left',right',fields',extra',hN,hN,hq',rfl⟩
  obtain ⟨output,run,ready,_⟩:=PhysicalIndexedExists.run_down_padded (260 : Fin 298) (levelBody provider levelProvider)
    depth E R (levelH (fun _=>0)) rfl hdepth (LevelReady C R N depth table Q) input hinput
    (by intro i _ t ht;obtain ⟨ci,pi,left,right,fields,extra,_,_,_,rfl⟩:=ht;rfl) step
  exact ⟨output,by simpa only [machine] using run,ready⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
