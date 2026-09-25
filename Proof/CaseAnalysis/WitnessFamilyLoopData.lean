import Proof.CaseAnalysis.WitnessFamilyRound

/-! The exact outer list addresses one sum per source variable. Its
invariant carries only the zero accumulator and the three ordered
logical streams. The successor bank is projected from the same receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def entry {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L k : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts : List Bool)
    (word : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  let coeffs:=TermLoop.emitted (FamilyRound.coefficientWord C) words out j
  let natives:=TermLoop.emitted (FamilyRound.nativeWord word) words native j
  let counters:=TermLoop.emitted FamilyRound.countWord words counts j
  (⟨(FamilyRound.machine circuit k q).start,
    FamilyLoad.heads (TermLoop.position words pre j) (SumDock.heads coeffs natives counters),
    FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity coeffs natives counters ambient)
      (pre++words.flatMap frame++tail)⟩ : Configuration 3063 _)

def passed (C T : ℕ) (q : ℚ) (words : List (List Bool)) (arity : List Bool) (circuitPass : List Bool → Bool):=
  words.all (fun bits=>SumRound.passed C T q bits arity circuitPass)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
