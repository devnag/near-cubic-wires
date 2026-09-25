import Proof.Assembly.Start

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJ93d4cfe17dc847a3

namespace Construction
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open PCJc4297ab269d8423a_Source

def fuel (d : MaskData) := 4*d.q+5+1+(1+1+(d.q*(Loop.bodyFuel d+3)+3))

theorem fuel_bound (d : MaskData) : fuel d ≤ maskBudget 256 4 d := by
  let B := d.q+d.K+d.m+d.supportWord.length+1
  have hq : d.q ≤ B := by dsimp [B]; omega
  have hm : d.m ≤ B := by dsimp [B]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hqm : d.q*d.m ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul hq hm
  have hqq : d.q*d.q ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul hq hq
  have hqqm : d.q*d.m*d.q ≤ B^3 := by
    calc
      _ ≤ B^2*B := Nat.mul_le_mul hqm hq
      _ = _ := by ring
  have h2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h1 : B ≤ B^4 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 4 by decide)
  have h0 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  change fuel d ≤ 256*B^4
  unfold fuel Loop.bodyFuel Reset.fuel
  nlinarith

theorem raw_step (d : MaskData) :
    Step Program.machine (fuel d) (fun _ => 0) (d.input 9)
      (RepeatMachine.cfg 3 (Loop.state d d.q []) d.q 1).heads
      (RepeatMachine.cfg 3 (Loop.state d d.q []) d.q 1).tapes := by
  obtain ⟨r,hr,hf,_⟩ := Loop.outer_run d
  have loop := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  exact (Start.init_step d).seq ((Start.setup_step d).seq loop)

theorem output (d : MaskData) :
    (RepeatMachine.cfg 3 (Loop.state d d.q []) d.q 1).tapes (4 : Fin 14) = d.word := by
  change (Winner.scan d d.q).2 = d.word
  exact Winner.winner_eq d

noncomputable def rawProducer : RawProducer where
  work := 9
  states := _
  machine := Program.machine
  coefficient := 256
  degree := 4
  correct := by
    intro d
    obtain ⟨r,hr,_,ha,_⟩ := (raw_step d).enlarge (fuel_bound d)
    exact ⟨r,hr,congrFun ha 4 |>.trans (output d)⟩

end Construction

theorem raw : RawConstruction := ⟨Construction.rawProducer, trivial⟩

end PCJ93d4cfe17dc847a3
