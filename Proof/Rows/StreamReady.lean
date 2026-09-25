import Proof.Rows.StreamPairPorts

/-! One paid bounded rewind restores both produced streams, their actual
count tape, and the original native source. Then move count head to one. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_StreamPair
open PCJ45bee56da9f34d5a_StreamPairPorts
noncomputable section

def rewind:=RecoveryFocus.machine readSlots (PCJ45bee56da9f34d5a_HeaderRewind.machine 4)
def moves (i :Fin 250):HeadMove:=if i=122 then .right else .stay
def right:=DecompositionCountPosition.move moves
def machine:=Composition.machine rewind right
def rewound (H :Fin 250→Nat):=dockH readSlots H (fun _=>0)
def heads (H :Fin 250→Nat) (i :Fin 250):=(moves i).apply (rewound H i)

theorem prepare (H :Fin 250→Nat) (A :Fin 250→List Bool) (Q U :Nat) (gs cs source :List Bool)
 (hheads :(fun i=>H (readSlots i))=(![Q,Q+1,cs.length,source.length,0,0] :Fin 6→Nat))
 (hwords :(fun i=>A (readSlots i))=(![gs,CompareMachine.word Q,cs,source,List.replicate U true,List.replicate (U+1) false] :Fin 6→List Bool))
 (hQ :Q+1≤U) (hcs :cs.length≤U) (hs :source.length≤U):
 Step machine (2*U+6) H A (heads H) A :=by
 let HH:Fin 4→Nat:=![Q,Q+1,cs.length,source.length]
 let AA:Fin 4→List Bool:=![gs,CompareMachine.word Q,cs,source]
 have hH:∀i,HH i≤U:=by
  intro i;fin_cases i
  · exact (Nat.le_succ Q).trans hQ
  · exact hQ
  · exact hcs
  · exact hs
 have rr:=(PCJ45bee56da9f34d5a_HeaderRewind.run 4 HH AA U hH).dock readSlots readSlots_injective H A
  (by intro i;have h:=congrFun hheads i;fin_cases i <;>exact h)
  (by intro i;have h:=congrFun hwords i;fin_cases i <;>exact h)
 have first:Step rewind (2*U+4) H A (rewound H) A:=by
  apply rr.congr rfl
  exact install_existing readSlots A _ (by intro i;have h:=congrFun hwords i;fin_cases i <;>exact h)
 obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run moves (rewound H) A
 have second:Step right 1 (rewound H) A (heads H) A:=
  Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
 have all:=first.seq second
 simpa only [machine,show (2*U+4)+1+1=2*U+6 by omega] using all

theorem head_slots (H :Fin 250→Nat) (i :Fin 6):
 heads H (readSlots i)=(![0,1,0,0,0,0] :Fin 6→Nat) i :=by
 unfold heads rewound
 rw [dockH_slot readSlots readSlots_injective]
 fin_cases i <;>rfl

theorem head_other (H :Fin 250→Nat) (i :Fin 250) (hi :∀j,readSlots j≠i):heads H i=H i :=by
 have h122:i≠122:=fun h=>hi 1 h.symm
 simp only [heads,moves,if_neg h122,HeadMove.apply,rewound]
 exact dockH_other readSlots H _ i hi

variable (a :DecompositionAlgorithm) (r :FourfoldRequest NormalizedThresholdThresholdCircuit)
 (four :r.circuits.length ≤ 4) (sel :ThresholdRows.Selection a r) (I :Finset (Fin r.q)) (x :BitInput r.q)
 (T L target p w F U v o :Nat)

theorem run (hQ :(flags r I x).length+1≤U)
 (hcs :(coefficientWord (data a r four sel) (radix a r four sel) p w o).length≤U)
 (hs :(native r L target).length≤U):
 Step machine (2*U+6) (outputHeads a r four sel I x L target p w o)
  (output a r four sel I x T L target p w F U v o)
  (heads (outputHeads a r four sel I x L target p w o))
  (output a r four sel I x T L target p w F U v o) :=
 prepare _ _ (flags r I x).length U (flags r I x)
  (coefficientWord (data a r four sel) (radix a r four sel) p w o) (native r L target)
  (read_heads a r four sel I x L target p w o) (read_words a r four sel I x T L target p w F U v o) hQ hcs hs
end
end PCJ45bee56da9f34d5a_StreamReady
