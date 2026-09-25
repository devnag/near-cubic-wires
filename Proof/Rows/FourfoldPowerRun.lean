import Proof.Rows.FourfoldPowerCell
import Proof.Rows.FourfoldPowerData

/-! Four guarded actual selected coefficient calls, with one power update per
active circuit and restored circuit-count cursor. Absent circuits emit nothing. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data words_length)
open PCJ45bee56da9f34d5a_FourfoldPowerData
open PCJ45bee56da9f34d5a_FourfoldPowerCell (bank heads)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_FourfoldPowerCell.machine

def guard (j :Fin 4):=CloseoutRowsOriginalSwitch.machine (PCJ45bee56da9f34d5a_FourfoldPowerCell.machine j)
 (CloseoutRowsOriginalSwitch.stop 110) 109
def advance:=DecompositionCountPosition.move (fun i :Fin 110=>if i=109 then .right else .stay)
def left:=DecompositionCountPosition.move (fun i :Fin 110=>if i=109 then .left else .stay)
def restore:=Composition.machine (Composition.machine (Composition.machine left left) left) left
def phase (j :Fin 4):=Composition.machine (guard j) advance
def machine:=Composition.machine
 (Composition.machine (Composition.machine (Composition.machine (phase 0) (phase 1)) (phase 2)) (phase 3)) restore

theorem advance_run (source :List Bool) (digits :Fin 4→Nat) (N a B p w F U v pos :Nat) (out :List Bool):
 Step advance 1 (heads out.length pos) (bank source digits N a B p w F U v out)
  (heads out.length (pos+1)) (bank source digits N a B p w F U v out) :=by
 obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
  (fun i :Fin 110=>if i=109 then .right else .stay) (heads out.length pos) (bank source digits N a B p w F U v out)
 apply (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
 · funext i;by_cases hi:i=109 <;>simp [heads,hi,HeadMove.apply]
 · rfl

theorem left_run (source :List Bool) (digits :Fin 4→Nat) (N a B p w F U v pos :Nat) (out :List Bool):
 Step left 1 (heads out.length (pos+1)) (bank source digits N a B p w F U v out)
  (heads out.length pos) (bank source digits N a B p w F U v out) :=by
 obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
  (fun i :Fin 110=>if i=109 then .left else .stay) (heads out.length (pos+1)) (bank source digits N a B p w F U v out)
 apply (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
 · funext i;by_cases hi:i=109 <;>simp [heads,hi,HeadMove.apply]
 · rfl

theorem restore_run (source :List Bool) (digits :Fin 4→Nat) (N a B p w F U v :Nat) (out :List Bool):
 Step restore 7 (heads out.length 5) (bank source digits N a B p w F U v out)
  (heads out.length 1) (bank source digits N a B p w F U v out) :=by
 exact (((left_run source digits N a B p w F U v 4 out).seq
  (left_run source digits N a B p w F U v 3 out)).seq
  (left_run source digits N a B p w F U v 2 out)).seq
  (left_run source digits N a B p w F U v 1 out)

theorem false_run (j :Fin 4) (source :List Bool) (digits :Fin 4→Nat)
 (N a B p w F U v :Nat) (out :List Bool) (hN :N≤j.val):
 Step (guard j) 2 (heads out.length (j.val+1)) (bank source digits N a B p w F U v out)
  (heads out.length (j.val+1)) (bank source digits N a B p w F U v out) :=by
 let cfg:Configuration 110 1:=⟨0,heads out.length (j.val+1),bank source digits N a B p w F U v out⟩
 let r:ExecutionReceipt 110 1:=⟨cfg,0,cfg.tapeCells⟩
 have h:Step (CloseoutRowsOriginalSwitch.stop 110) 0 (heads out.length (j.val+1)) (bank source digits N a B p w F U v out)
  (heads out.length (j.val+1)) (bank source digits N a B p w F U v out):=
  Step.of_run (show runFrom (CloseoutRowsOriginalSwitch.stop 110) 0 cfg=some r from rfl) rfl rfl
 apply CloseoutRowsOriginalSwitch.false_run _ _ _ h
 change readTapeBit (ZeroPadding.pad U (UnaryTemplate.tape N)) (j.val+1)=false
 rw [ZeroPadding.read_pad,CloseoutRowsGateTemplateCheck.template_read]
 simp only [decide_eq_false_iff_not];omega

theorem phase_run (d :Data) (B p w F U v C P :Nat) (hb :Bounds d B p w F U v C P)
 (out :List Bool) (j :Fin 4):
 Step (phase j) (P+4)
  (heads (out++stream d B p w j.val).length (j.val+1))
  (bank (d.words.flatMap frame) d.digits d.count (factor d B p j.val) B p w F U v (out++stream d B p w j.val))
  (heads (out++stream d B p w (j.val+1)).length (j.val+2))
  (bank (d.words.flatMap frame) d.digits d.count (factor d B p (j.val+1)) B p w F U v (out++stream d B p w (j.val+1))) :=by
 by_cases hj:j.val<d.count
 · let k:Fin d.count:=⟨j.val,hj⟩
   let circuit:Fin d.words.length:=⟨j.val,by simpa using hj⟩
   have hlocal:=hb.local_fit k
   have chosen:d.words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload (d.gates k):=by
    simp [Data.words,List.get_eq_getElem,circuit,k]
   have digit:d.digits j=(d.selected k).val:=by simp [Data.digits,hj,k]
   have base:=PCJ45bee56da9f34d5a_FourfoldPowerCell.run j d.digits (j.val+1) d.words circuit C
    (d.gates k) (d.selected k) (factor d B p j.val) B p w F U v (out++stream d B p w j.val)
    rfl digit hb.payloads (hb.top_cost circuit) chosen hlocal.arity_cost hlocal.digit_fit hlocal.digit_cost
    hlocal.payload_fit hlocal.cursor_cost hlocal.gate_fit hb.positive hb.prime_fit
    (factor_lt d B p w j.val hb.positive hb.prime_fit) hb.base_fit hlocal.weight_cost hlocal.target_cost hb.capacity
   simp only [words_length] at base
   have guarded:=CloseoutRowsOriginalSwitch.true_run _ (CloseoutRowsOriginalSwitch.stop 110) 109 base
    (by
     change readTapeBit (ZeroPadding.pad U (UnaryTemplate.tape d.count)) (j.val+1)=true
     rw [ZeroPadding.read_pad]
     exact UnaryTemplate.tape_mark _ _ (by omega))
   have step:Step (guard j) (P+2)
    (heads (out++stream d B p w j.val).length (j.val+1))
    (bank (d.words.flatMap frame) d.digits d.count (factor d B p j.val) B p w F U v (out++stream d B p w j.val))
    (heads (out++stream d B p w (j.val+1)).length (j.val+1))
    (bank (d.words.flatMap frame) d.digits d.count (factor d B p (j.val+1)) B p w F U v (out++stream d B p w (j.val+1))):=by
     have more:=guarded.enlarge (Nat.add_le_add_right (hb.cell_cost k) 2)
     simpa only [guard,k,factor,stream,if_pos hj,dif_pos hj,List.append_assoc] using more
   exact step.seq (advance_run (d.words.flatMap frame) d.digits d.count (factor d B p (j.val+1)) B p w F U v (j.val+1) (out++stream d B p w (j.val+1)))
 · have step:=(false_run j (d.words.flatMap frame) d.digits d.count (factor d B p j.val) B p w F U v
     (out++stream d B p w j.val) (by omega)).enlarge (show 2≤P+2 by omega)
   have last:=advance_run (d.words.flatMap frame) d.digits d.count (factor d B p j.val) B p w F U v (j.val+1)
     (out++stream d B p w j.val)
   simpa only [phase,factor,stream,if_neg hj,dif_neg hj] using step.seq last

theorem run (d :Data) (B p w F U v C P :Nat) (hb :Bounds d B p w F U v C P) (out :List Bool):
 Step machine (4*P+27) (heads out.length 1) (bank (d.words.flatMap frame) d.digits d.count 1 B p w F U v out)
  (heads (out++stream d B p w 4).length 1)
  (bank (d.words.flatMap frame) d.digits d.count (factor d B p 4) B p w F U v (out++stream d B p w 4)) :=by
 have all:=((((phase_run d B p w F U v C P hb out 0).seq (phase_run d B p w F U v C P hb out 1)).seq
  (phase_run d B p w F U v C P hb out 2)).seq (phase_run d B p w F U v C P hb out 3)).seq
  (restore_run (d.words.flatMap frame) d.digits d.count (factor d B p 4) B p w F U v (out++stream d B p w 4))
 simp only [show factor d B p (0 :Fin 4).val=1 from rfl,
  show stream d B p w (0 :Fin 4).val=[] from rfl,List.append_nil] at all
 unfold machine
 convert all using 1 <;>first |rfl |omega
end
end PCJ45bee56da9f34d5a_FourfoldPowerRun
