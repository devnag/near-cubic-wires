import Proof.Rows.NativeCircuitFlags

/-! Resident original circuit stream plus one reusable frame buffer. Unwrapping
reuses the copy log; the full resident stream never enters the gate reserve. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitFlagBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds
noncomputable section

def heads (pos cursor : Nat) (out : List Bool) (Q count : Nat) : Fin 127→Nat :=
 Fin.addCases (m:=124) (n:=3) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_NativeCircuitCount.heads pos out Q count) ![cursor,0,0]
def bank {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B : Nat)
 (source raw framed out count : List Bool) (Q : Nat) : Fin 127→List Bool :=
 Fin.addCases (m:=124) (n:=3) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x (B+1) (H B q (B+1)) (R B q (B+1)) (U B q (B+1))
   (ZeroPadding.pad (U B q (B+1)) raw) (List.replicate (H B q (B+1)) false)
   (List.replicate (H B q (B+1)) false) out count Q)
  ![source,ZeroPadding.pad (U B q (B+1)) framed,List.replicate (U B q (B+1)) false]

def caps (U : Nat) (i : Fin 124) :=if i=114 then U else 0

theorem inner_source_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q : Nat)
 (source source' fields framed out count : List Bool) (i : Fin 124) (hi : i≠114) :
 PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x w H R U source fields framed out count Q i=
 PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x w H R U source' fields framed out count Q i := by
 revert hi
 refine Fin.addCases (m:=123) (n:=1) (fun a ha=>?_) (fun _ _=>?_) i
 · revert ha
   refine Fin.addCases (m:=122) (n:=1) (fun b hb=>?_) (fun _ _=>?_) a
   · revert hb
     refine Fin.addCases (m:=114) (n:=8) (fun _ _=>?_) (fun c hc=>?_) b
     · simp only [PCJ45bee56da9f34d5a_NativeCircuitCount.bank,PCJ45bee56da9f34d5a_CountedGateCell.bank,
         PCJ45bee56da9f34d5a_FramedGateBank.bank,Fin.addCases_left]
     · fin_cases c <;>first | exact False.elim (hc rfl) | rfl
   · simp only [PCJ45bee56da9f34d5a_NativeCircuitCount.bank,PCJ45bee56da9f34d5a_CountedGateCell.bank,Fin.addCases_left,Fin.addCases_right]
 · simp only [PCJ45bee56da9f34d5a_NativeCircuitCount.bank,Fin.addCases_right]

theorem inner_pad {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (w H R U Q : Nat)
 (source fields framed out count : List Bool) :
 (fun i=>ZeroPadding.pad (caps U i) (PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x w H R U source fields framed out count Q i))=
 PCJ45bee56da9f34d5a_NativeCircuitCount.bank live x w H R U (ZeroPadding.pad U source) fields framed out count Q := by
 funext i
 by_cases hi:i=114
 · subst i;rfl
 · simp only [caps,if_neg hi,ZeroPadding.pad_zero]
   exact inner_source_away live x w H R U Q _ _ _ _ _ _ i hi

theorem heads_away (pos cursor cursor' Q count : Nat) (out : List Bool) (i : Fin 127) (hi : i≠124) :
 heads pos cursor out Q count i=heads pos cursor' out Q count i := by
 revert hi
 refine Fin.addCases (m:=124) (n:=3) (fun _ _=>?_) (fun j hj=>?_) i
 · simp only [heads,Fin.addCases_left]
 · fin_cases j <;>first | exact False.elim (hj rfl) | rfl

theorem frame_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (source raw framed framed' out count : List Bool) (i : Fin 127) (hi : i≠125) :
 bank live x B source raw framed out count Q i=bank live x B source raw framed' out count Q i := by
 revert hi
 refine Fin.addCases (m:=124) (n:=3) (fun _ _=>?_) (fun j hj=>?_) i
 · simp only [bank,Fin.addCases_left]
 · fin_cases j <;>first | exact False.elim (hj rfl) | rfl

theorem raw_away {q : Nat} (live : Finset (Fin q)) (x : BitInput q) (B Q : Nat)
 (source raw raw' framed out count : List Bool) (i : Fin 127) (hi : i≠114) :
 bank live x B source raw framed out count Q i=bank live x B source raw' framed out count Q i := by
 revert hi
 refine Fin.addCases (m:=124) (n:=3) (fun j hj=>?_) (fun _ _=>?_) i
 · simp only [bank,Fin.addCases_left]
   exact inner_source_away live x _ _ _ _ Q _ _ _ _ _ _ j (fun he=>hj (congrArg (fun k :Fin 124=>k.castAdd 3) he))
 · simp only [bank,Fin.addCases_right]
end
end PCJ45bee56da9f34d5a_CircuitFlagBank
