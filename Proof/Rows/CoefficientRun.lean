import Proof.Rows.ThresholdStreams

/-! Physically compose all four selected TOP blocks with the final unscaled
binary offset append on the same growing output tape. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CoefficientRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
open PCJ45bee56da9f34d5a_FourfoldPowerData
noncomputable section

def extra (p w U o :Nat):Fin 12→List Bool:=fun i=>
 PCJ45bee56da9f34d5a_OffsetEmitter.cold (PCJ45bee56da9f34d5a_OffsetEmitter.palette p w o) U [] (i.castAdd 1)
def bank (d :Data) (a B p w F U v o :Nat) (out :List Bool):Fin 122→List Bool:=
 Fin.addCases (m:=110) (n:=12) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_FourfoldPowerCell.bank (d.words.flatMap frame) d.digits d.count a B p w F U v out)
  (extra p w U o)
def heads (len :Nat):Fin 122→Nat:=Fin.addCases (m:=110) (n:=12) (motive:=fun _=>Nat)
 (PCJ45bee56da9f34d5a_FourfoldPowerCell.heads len 1) (fun _=>0)
def offsetSlots (i :Fin 13):Fin 122:=if h:i.val<12 then ⟨110+i.val,by omega⟩ else 64
theorem offsetSlots_injective:Function.Injective offsetSlots:=by decide

def first:=TapeEmbedding.machine 12 PCJ45bee56da9f34d5a_FourfoldPowerRun.machine
def last:=RecoveryFocus.machine offsetSlots PCJ45bee56da9f34d5a_OffsetEmitter.machine
def machine:=Composition.machine first last

def output (d :Data) (B p w F U v o :Nat) (out :List Bool):Fin 122→List Bool:=
 install offsetSlots
  (bank d (factor d B p 4) B p w F U v o (out++stream d B p w 4))
  (PCJ45bee56da9f34d5a_OffsetEmitter.cold (PCJ45bee56da9f34d5a_OffsetEmitter.palette p w o) U
   ((out++stream d B p w 4)++frame (binary w ((p-o)%p))))
def finalHeads (d :Data) (B p w o :Nat) (out :List Bool):Fin 122→Nat:=
 dockH offsetSlots (heads (out++stream d B p w 4).length)
  (PCJ45bee56da9f34d5a_OffsetEmitter.heads
   ((out++stream d B p w 4)++frame (binary w ((p-o)%p))).length 0)

theorem slots_heads (len :Nat) (i :Fin 13):
 heads len (offsetSlots i)=PCJ45bee56da9f34d5a_OffsetEmitter.heads len 0 i :=by
 fin_cases i <;>rfl

theorem slots_bank (d :Data) (a B p w F U v o :Nat) (out :List Bool) (i :Fin 13):
 bank d a B p w F U v o out (offsetSlots i)=
 PCJ45bee56da9f34d5a_OffsetEmitter.cold (PCJ45bee56da9f34d5a_OffsetEmitter.palette p w o) U out i :=by
 fin_cases i
 all_goals first
  | rfl
  | change ZeroPadding.pad 0 (ZeroPadding.pad 0 (ZeroPadding.pad 0 out))=out
    simp only [ZeroPadding.pad_zero]

theorem run (d :Data) (B p w F U v C P o :Nat) (hb :Bounds d B p w F U v C P)
 (ho :o<p) (out :List Bool):
 Step machine ((4*P+27)+1+(6*U+10*w+28)) (heads out.length)
  (bank d 1 B p w F U v o out) (finalHeads d B p w o out) (output d B p w F U v o out) :=by
 have firstStep:=(PCJ45bee56da9f34d5a_FourfoldPowerRun.run d B p w F U v C P hb out).embed
  (fun _ :Fin 12=>0) (extra p w U o)
 have hu:2*w+2≤U:=by
  have h:=hb.capacity
  nlinarith [Nat.zero_le (w*w)]
 have secondStep:=(PCJ45bee56da9f34d5a_OffsetEmitter.run p w U o (out++stream d B p w 4)
  hb.positive hb.prime_fit ho hu).dock offsetSlots offsetSlots_injective
  (heads (out++stream d B p w 4).length)
  (bank d (factor d B p 4) B p w F U v o (out++stream d B p w 4))
  (slots_heads _) (slots_bank d _ B p w F U v o _)
 exact firstStep.seq secondStep

theorem output_word (d :Data) (B p w F U v o :Nat) (out :List Bool):
 output d B p w F U v o out 64=(out++stream d B p w 4)++frame (binary w ((p-o)%p)) :=by
 change output d B p w F U v o out (offsetSlots 12)=_
 unfold output
 rw [install_slot offsetSlots offsetSlots_injective]
 rfl
end
end PCJ45bee56da9f34d5a_CoefficientRun
