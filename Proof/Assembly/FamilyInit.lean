import Proof.Assembly.Generator

/-! A concrete two-stage generator: descriptor/scalar production followed by
one blank-bank initializer. The initializer is uniform in runtime values.
Its certified physical interface and cost are consumed by the front proof.
No input or execution witness is inserted into the literal theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ515eaa990d75455b_FamilyInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ1fef9807c6954e94_Native

/-- Values are runtime data, not parameters of the initializer's code.
The front also physically computes the N*b driver. -/
structure Scalars where
  S : Nat
  R : Nat
  B : Nat
  b : Nat
  v : Nat
  N : Nat

@[irreducible] noncomputable def initTapes (a : WilliamsAlgorithm) : Nat := r_tapes a+7

def drivers (m : Scalars) : Fin 7 → List Bool :=
  ![CompareMachine.word m.S, CompareMachine.word m.R,
    CompareMachine.word m.B, CompareMachine.word m.b,
    CompareMachine.word m.v, CompareMachine.word m.N,
    CompareMachine.word (m.N*m.b)]

noncomputable def sourcePort (a : WilliamsAlgorithm) : Fin (r_tapes a) :=
  ⟨P1TopDownPaidPayload.tapes a+3, by unfold r_tapes; omega⟩

noncomputable def entryH (a : WilliamsAlgorithm) : Fin (initTapes a) → Nat := by
  unfold initTapes
  exact Fin.addCases (fun _ : Fin (r_tapes a) => 0) (fun _ : Fin 7 => 1)

/-- Family destinations are genuinely blank, except the retained descriptor
stream already at its final source port. All seven numeric drivers are paid
outputs of the preceding stage. No private log occupies a required-empty port. -/
noncomputable def entry (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (initTapes a) → List Bool := by
  unfold initTapes
  exact Fin.addCases (fun i : Fin (r_tapes a) => if i=sourcePort a then D else []) (drivers m)

noncomputable def familyBank (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (r_tapes a) → List Bool :=
  Fin.addCases
    (Fin.addCases (P1TopDownPaidReusable.bank a D m.S m.R m.B [])
      (fun _ : Fin 1 => CompareMachine.word m.N))
    (P1TopDownPaidFamilySum.extra m.b m.v m.N)

noncomputable def exitH (a : WilliamsAlgorithm) : Fin (initTapes a) → Nat := by
  unfold initTapes
  exact Fin.addCases (r_inputH a [] 0 0 0 0) (fun _ : Fin 7 => 1)

noncomputable def exitT (a : WilliamsAlgorithm) (m : Scalars) (D : List Bool) :
    Fin (initTapes a) → List Bool := by
  unfold initTapes
  exact Fin.addCases (familyBank a m D) (drivers m)

/-- A fixed linear allowance for all blank allocation, copies, framing and
head restoration. It is charged once per whole generated family. -/
noncomputable def initFuel (a : WilliamsAlgorithm) (m : Scalars) : Nat :=
  1000*(r_tapes a+1)*(m.S+m.R+m.B+m.b+m.v+m.N+m.N*m.b+1)

/-- Prefix code starts at the actual nine-word Input bank. Its result carries
semantic fields and its complete physical exit, before initialization. -/
structure PrefixCode where
  printer : WilliamsAlgorithm
  scratch : Nat
  states : Nat
  machine : Machine (PCJf990607ff5714139_Generator.tapes printer (7+scratch)) states
  policy : PCJf990607ff5714139_Generator.Policy
  result : PCJf990607ff5714139_Generator.Input → PCJf990607ff5714139_Generator.Result (PCJf990607ff5714139_Generator.tapes printer (7+scratch))

end PCJ515eaa990d75455b_FamilyInit
