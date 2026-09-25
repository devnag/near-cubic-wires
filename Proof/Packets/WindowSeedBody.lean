import Proof.Packets.WindowSeedFinish

/-! The fixed window initialization program physically constructs every
private scalar and loop driver from seven retained numeric metadata tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

@[simp] theorem pad_idem (R : Nat) (word : List Bool) :
    ZeroPadding.pad R (ZeroPadding.pad R word)=ZeroPadding.pad R word := by
  change ZeroPadding.pad R word++List.replicate (R-(ZeroPadding.pad R word).length) false=_
  rw [ZeroPadding.pad_length,Nat.sub_eq_zero_of_le (Nat.le_max_left _ _)]
  simp

def metadata (R v u M offset W target : Nat) : Fin 7→List Bool :=
  ![ZeroPadding.pad R (frame (binary u offset)),ZeroPadding.pad R (frame (binary u (2*W))),
    ZeroPadding.pad R (frame (binary u target)),source R u,source R M,source R v,source R W]
def initial (R v u M offset W target : Nat) : Fin 69→List Bool :=
  Fin.addCases (m:=62) (n:=7) (fun i=>if i=50 then List.replicate R true else
    if i=51 then List.replicate (R+3) false else List.replicate R false)
    (metadata R v u M offset W target)

def updates (R v u M offset W target : Nat) : List (Fin 69 × List Bool) :=
  [(46,source R v),
    (49,ZeroPadding.pad R (List.replicate v true)),
    (59,ZeroPadding.pad R (List.replicate M true)),
    (53,ZeroPadding.pad R (frame (binary u 0))),
    (54,ZeroPadding.pad R (frame (binary u 0))),
    (57,ZeroPadding.pad R (frame (binary u 0))),
    (52,ZeroPadding.pad R (frame (binary u offset))),
    (58,ZeroPadding.pad R (frame (binary u target))),
    (47,ZeroPadding.pad R (frame (binary v 0))),
    (60,source R M),
    (60,source R (M-1)),
    (47,ZeroPadding.pad R (frame (binary v (M-1)))),
    (60,List.replicate R false),
    (61,source R (2*W+1))]
def produced (R v u M offset W target : Nat) :=
  (updates R v u M offset W target).foldl (fun A e=>Function.update A e.1 e.2)
    (initial R v u M offset W target)
def body := Composition.machine (copyAt 67 46) (Composition.machine (rawAt 67 49) (Composition.machine (rawAt 66 59) (Composition.machine (zeroAt 65 53) (Composition.machine (copyAt 53 54) (Composition.machine (copyAt 53 57) (Composition.machine (copyAt 62 52) (Composition.machine (copyAt 64 58) (Composition.machine (zeroAt 67 47) (Composition.machine (copyAt 66 60) (Composition.machine (predAt 60) (Composition.machine (valueAt 60 47) (Composition.machine (clearOneAt 60) (widthAt)))))))))))))
def bodyBudget (R v u M W : Nat) := (2*R+4)+1+((2*v+6)+1+((2*M+6)+1+((8*u+11)+1+((2*R+4)+1+((2*R+4)+1+((2*R+4)+1+((2*R+4)+1+((8*v+11)+1+((2*R+4)+1+((2*M+7)+1+((ScalarFromCounter.budget v (M-1)+4)+1+((2*R+4)+1+(WindowWidthDriver.budget W)))))))))))))

theorem body_run (R v u M offset W target : Nat)
    (hu : 2*u+1≤R) (hv : 2*v+1≤R) (hM : M+1≤R) (hMv : M≤2^v) :
    Step body (bodyBudget R v u M W) (fun _=>0) (initial R v u M offset W target)
      (fun _=>0) (produced R v u M offset W target) := by
  let A0:=initial R v u M offset W target
  let A1:=Function.update A0 (46 : Fin 69) (source R v)
  let A2:=Function.update A1 (49 : Fin 69) (ZeroPadding.pad R (List.replicate v true))
  let A3:=Function.update A2 (59 : Fin 69) (ZeroPadding.pad R (List.replicate M true))
  let A4:=Function.update A3 (53 : Fin 69) (ZeroPadding.pad R (frame (binary u 0)))
  let A5:=Function.update A4 (54 : Fin 69) (ZeroPadding.pad R (frame (binary u 0)))
  let A6:=Function.update A5 (57 : Fin 69) (ZeroPadding.pad R (frame (binary u 0)))
  let A7:=Function.update A6 (52 : Fin 69) (ZeroPadding.pad R (frame (binary u offset)))
  let A8:=Function.update A7 (58 : Fin 69) (ZeroPadding.pad R (frame (binary u target)))
  let A9:=Function.update A8 (47 : Fin 69) (ZeroPadding.pad R (frame (binary v 0)))
  let A10:=Function.update A9 (60 : Fin 69) (source R M)
  let A11:=Function.update A10 (60 : Fin 69) (source R (M-1))
  let A12:=Function.update A11 (47 : Fin 69) (ZeroPadding.pad R (frame (binary v (M-1))))
  let A13:=Function.update A12 (60 : Fin 69) (List.replicate R false)
  let A14:=Function.update A13 (61 : Fin 69) (source R (2*W+1))
  have h1 : Step (copyAt 67 46) (2*R+4) (fun _=>0) A0 (fun _=>0) A1 := by
    have hs : A0 67=source R v := by simp [A0, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 67 46 A0 (by decide) (by simp [A0, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A1, hs, source, pad_idem] using h
  have h2 : Step (rawAt 67 49) (2*v+6) (fun _=>0) A1 (fun _=>0) A2 := by
    exact raw_at R v 67 49 A1 (by decide) (by omega) (by simp [A0, A1, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h3 : Step (rawAt 66 59) (2*M+6) (fun _=>0) A2 (fun _=>0) A3 := by
    exact raw_at R M 66 59 A2 (by decide) (by omega) (by simp [A0, A1, A2, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h4 : Step (zeroAt 65 53) (8*u+11) (fun _=>0) A3 (fun _=>0) A4 := by
    exact zero_at R u 65 53 A3 (by decide) (by omega) (by simp [A0, A1, A2, A3, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h5 : Step (copyAt 53 54) (2*R+4) (fun _=>0) A4 (fun _=>0) A5 := by
    have hs : A4 53=ZeroPadding.pad R (frame (binary u 0)) := by simp [A0, A1, A2, A3, A4, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 53 54 A4 (by decide) (by simp [A0, A1, A2, A3, A4, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A5, hs, source, pad_idem] using h
  have h6 : Step (copyAt 53 57) (2*R+4) (fun _=>0) A5 (fun _=>0) A6 := by
    have hs : A5 53=ZeroPadding.pad R (frame (binary u 0)) := by simp [A0, A1, A2, A3, A4, A5, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 53 57 A5 (by decide) (by simp [A0, A1, A2, A3, A4, A5, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, A5, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A6, hs, source, pad_idem] using h
  have h7 : Step (copyAt 62 52) (2*R+4) (fun _=>0) A6 (fun _=>0) A7 := by
    have hs : A6 62=ZeroPadding.pad R (frame (binary u offset)) := by simp [A0, A1, A2, A3, A4, A5, A6, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 62 52 A6 (by decide) (by simp [A0, A1, A2, A3, A4, A5, A6, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, A5, A6, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A7, hs, source, pad_idem] using h
  have h8 : Step (copyAt 64 58) (2*R+4) (fun _=>0) A7 (fun _=>0) A8 := by
    have hs : A7 64=ZeroPadding.pad R (frame (binary u target)) := by simp [A0, A1, A2, A3, A4, A5, A6, A7, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 64 58 A7 (by decide) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A8, hs, source, pad_idem] using h
  have h9 : Step (zeroAt 67 47) (8*v+11) (fun _=>0) A8 (fun _=>0) A9 := by
    exact zero_at R v 67 47 A8 (by decide) (by omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h10 : Step (copyAt 66 60) (2*R+4) (fun _=>0) A9 (fun _=>0) A10 := by
    have hs : A9 66=source R M := by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, initial, metadata, Fin.addCases, source]
    have h:=copy_at R 66 60 A9 (by decide) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
    simpa only [A10, hs, source, pad_idem] using h
  have h11 : Step (predAt 60) (2*M+7) (fun _=>0) A10 (fun _=>0) A11 := by
    exact pred_at R M 60 A10 hM (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h12 : Step (valueAt 60 47) (ScalarFromCounter.budget v (M-1)+4) (fun _=>0) A11 (fun _=>0) A12 := by
    exact value_at R v 0 (M-1) 60 47 A11 (by decide) (by have hp:=Nat.two_pow_pos v;omega) (by omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h13 : Step (clearOneAt 60) (2*R+4) (fun _=>0) A12 (fun _=>0) A13 := by
    exact clear_one_at R 60 A12 (by decide) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word] <;> omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  have h14 : Step (widthAt) (WindowWidthDriver.budget W) (fun _=>0) A13 (fun _=>0) A14 := by
    exact width_at R W A13 (by omega) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word]) (by simp [A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, initial, metadata, Fin.addCases, source, ZeroPadding.pad_length, frame_length, binary_length, CompareMachine.word])
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14)))))))))))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
