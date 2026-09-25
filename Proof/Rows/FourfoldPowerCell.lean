import Proof.Rows.CircuitPowerRun

/-! Four child digits and fixed circuit cursors share the actual reusable
coefficient cell. The only changing prefix tapes are factor28 and output64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CircuitPowerInput.machine

def extras (source :List Bool) (digits :Fin 4→Nat) (N v U :Nat):Fin 11→List Bool:=
 ![List.replicate v true,frame (binary v (digits 0)),frame (binary v (digits 1)),
 frame (binary v (digits 2)),frame (binary v (digits 3)),frame source,
 ZeroPadding.pad U (CompareMachine.word 0),ZeroPadding.pad U (CompareMachine.word 1),
 ZeroPadding.pad U (CompareMachine.word 2),ZeroPadding.pad U (CompareMachine.word 3),
 ZeroPadding.pad U (UnaryTemplate.tape N)]
def bank (source :List Bool) (digits :Fin 4→Nat) (N a B p w F U v :Nat) (out :List Bool):Fin 110→List Bool:=
 Fin.addCases (m:=99) (n:=11) (motive:=fun _=>List Bool)
  (fun i=>PCJ45bee56da9f34d5a_CircuitPowerInput.bank a B p w F U v 0 0 source [] out (i.castAdd 4))
  (extras source digits N v U)
def heads (len pos :Nat) (i :Fin 110):=if i=109 then pos else if (105 ≤ i.val ∧ i.val < 109) then 1 else if i=64 then len else 0

def slots (j :Fin 4) (i :Fin 103):Fin 110:=
 if h:i.val<99 then ⟨i.val,by omega⟩ else if i=99 then ⟨100+j.val,by omega⟩
 else if i=100 then 99 else if i=101 then 104 else ⟨105+j.val,by omega⟩
theorem slots_injective (j :Fin 4):Function.Injective (slots j):=by fin_cases j <;>decide
def machine (j :Fin 4):=RecoveryFocus.machine (slots j) PCJ45bee56da9f34d5a_CircuitPowerInput.machine

theorem prefix_eq (a B p w F U v key circuit :Nat) (source out :List Bool) (i :Fin 99):
 PCJ45bee56da9f34d5a_CircuitPowerInput.bank a B p w F U v key circuit source [] out (i.castAdd 4)=
 PCJ45bee56da9f34d5a_CircuitPowerInput.bank a B p w F U v 0 0 source [] out (i.castAdd 4) :=by
 have he:i.castAdd 4=(i.castAdd 2).castAdd 2:=rfl
 rw [he]
 simp only [PCJ45bee56da9f34d5a_CircuitPowerInput.bank,Fin.addCases_left,
   PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank]

theorem head_slot (j :Fin 4) (len pos :Nat) (i :Fin 103):
 heads len pos (slots j i)=PCJ45bee56da9f34d5a_CircuitPowerInput.heads len i :=by
 fin_cases j <;>fin_cases i <;>rfl

theorem bank_slot (j :Fin 4) (source :List Bool) (digits :Fin 4→Nat)
 (N a B p w F U v :Nat) (out :List Bool) (i :Fin 103):
 bank source digits N a B p w F U v out (slots j i)=
 PCJ45bee56da9f34d5a_CircuitPowerInput.bank a B p w F U v (digits j) j.val source [] out i :=by
 refine Fin.addCases (m:=99) (n:=4) (fun k=>?_) (fun k=>?_) i
 · have hs:slots j (k.castAdd 4)=k.castAdd 11:=by
    apply Fin.ext;simp only [slots,Fin.val_castAdd,dif_pos k.isLt]
   rw [hs]
   simp only [bank,Fin.addCases_left]
   exact (prefix_eq a B p w F U v (digits j) j.val source out k).symm
 · fin_cases j <;>fin_cases k <;>first |rfl |exact (ZeroPadding.pad_zero _).symm

theorem outside_prefix (j :Fin 4) (i :Fin 110) (hi :∀k,slots j k≠i):99 ≤ i.val :=by
 by_contra h
 have hlt:i.val<99:=by omega
 let k :Fin 103:=⟨i.val,by omega⟩
 apply hi k
 apply Fin.ext;simp [slots,k,hlt]

theorem run (j :Fin 4) (digits :Fin 4→Nat) (pos :Nat)
 (words :List (List Bool)) (circuit :Fin words.length) (C :Nat)
 {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length)
 (a B p w F U v :Nat) (out :List Bool)
 (hci : circuit.val=j.val) (hdigit : digits j=i.val)
 (hb :∀x∈words,x.length≤C) (htop :PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit C+2≤U)
 (hselected :words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
 (hu :PCPPQueryNatural.budget n<U) (hi :i.val<2^v) (hindex :MatrixUnaryTemplate.budget v i.val<U)
 (hpay :(PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
 (hf :PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U) (hg :(exactWord (gs.get i)).length+2≤U)
 (hp :0<p) (hpw :2*p≤2^w) (ha :a<2^w) (hB :B<2^w)
 (hw :∀k,C10NativeResidueCallback.coreBudget false ((gs.get i).weight k) w+1≤F)
 (ht :C10NativeResidueCallback.coreBudget true (gs.get i).target w+1≤F) (hU :1024*(w+1)^2+2≤U):
 Step (machine j) (PCJ45bee56da9f34d5a_CircuitPowerRun.budget words circuit C gs i w F U v)
  (heads out.length pos) (bank (words.flatMap frame) digits words.length a B p w F U v out)
  (heads (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i))).length pos)
  (bank (words.flatMap frame) digits words.length ((a*B)%p) B p w F U v
    (out++PCJ45bee56da9f34d5a_NativeScaleEquation.result a p w (equation (gs.get i)))) :=by
 have base:=PCJ45bee56da9f34d5a_CircuitPowerRun.run words circuit C gs i a B p w F U v out
  hb htop hselected hu hi hindex hpay hf hg hp hpw ha hB hw ht hU
 rw [hci,←hdigit] at base
 have h:=base.dock (slots j) (slots_injective j) (heads out.length pos)
  (bank (words.flatMap frame) digits words.length a B p w F U v out)
  (head_slot j _ _) (bank_slot j _ _ _ _ _ _ _ _ _ _ _)
 apply h.congr
 · apply PCJ45bee56da9f34d5a_NativeCircuitCount.dock_heads (slots j) (slots_injective j)
   · intro k;exact (head_slot j _ _ k).symm
   · intro k hk
     have hge:=outside_prefix j k hk
     have hn:k≠64:=by intro he;subst k;norm_num at hge
     simp only [heads,if_neg hn]
 · apply HierarchyAllocation.install_eq (slots j) (slots_injective j)
   · exact bank_slot j _ _ _ _ _ _ _ _ _ _ _
   · intro k hk
     have hge:=outside_prefix j k hk
     let z :Fin 11:=⟨k.val-99,by omega⟩
     have he:z.natAdd 99=k:=by apply Fin.ext;change 99+(k.val-99)=k.val;omega
     rw [←he];simp only [bank,Fin.addCases_right]
end
end PCJ45bee56da9f34d5a_FourfoldPowerCell
