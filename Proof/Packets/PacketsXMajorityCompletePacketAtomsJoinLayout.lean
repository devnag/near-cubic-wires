import Proof.Packets.PacketsXMajorityCompletePacketActualRun
import Proof.Packets.PacketsXMajorityCompletePacketAtomsDock

/-! Fixed58-tape join. The intermediate row polynomial is retained outside
the atom producer; two paid copies install it into the resulting arithmetic
arena. The substitution work tapes are disjoint fresh tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtomsJoin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair)
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

def extras (C R : Nat) (P : Ring.Poly Nat) : Fin 12→List Bool :=
  Fin.append (![PacketVector.payload R (P.map (maskNat C)),PacketVector.count R (P.map (maskNat C))] : Fin 2→List Bool)
    (fun _ : Fin 10=>[])
def heads : Fin 58→Nat := Fin.append DenseAtomBoundary.heads (fun _ : Fin 12=>0)
def input (C R : Nat) (cs : List Pair) (P : Ring.Poly Nat) : Fin 58→List Bool :=
  Fin.append (IdentityAtomMaterialize.input C R cs [] []) (extras C R P)
def before (C R : Nat) (cs : List Pair) (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) : Fin 58→List Bool :=
  Fin.append (AddressedAtomMaterialize.paddedA C R id cs (atoms.map (List.map (maskNat C))) 0) (extras C R P)
def copied (C R : Nat) (cs : List Pair) (atoms : List (Ring.Poly Nat)) (P : Ring.Poly Nat) :=
  Function.update (Function.update (before C R cs atoms P) 26
    (PacketVector.payload R (P.map (maskNat C)))) 27 (PacketVector.count R (P.map (maskNat C)))
def slots (i : Fin 45) : Fin 58 :=
  if h:i.val<34 then (PacketAtoms.arithmeticSlots ⟨i.val,h⟩).castAdd 12
  else if i.val=34 then 42 else ⟨i.val+13,by have hi:=i.isLt;omega⟩
theorem slots_injective : Function.Injective slots := by decide
def first := TapeEmbedding.machine 12 PacketAtoms.machine
def copy := PhysicalCopyPair.machine (33 : Fin 58) 46 26 47 27
def lower := RecoveryFocus.machine slots PacketRun.rewound
def machine := Composition.machine (Composition.machine first copy) lower


theorem right_words (C R : Nat) (P : Ring.Poly Nat) :
    Function.update (Function.update (ReusableArithmetic.natState C R [] []) 26
      (PacketVector.payload R (P.map (maskNat C)))) 27
      (PacketVector.count R (P.map (maskNat C)))=ReusableArithmetic.natState C R [] P := by
  funext i
  fin_cases i <;>simp [ReusableArithmetic.natState,ReusableArithmetic.state,
    ReusableArithmetic.bank,ReusableArithmetic.padded,ReusableArithmetic.data,
    NormalizedMultiply.data,NormalizedMultiply.extras,NormalizeCold.data,Normalize.records,
    Function.update,Fin.addCases,PacketVector.payload,PacketVector.count]

theorem core_words (C R : Nat) (cs : List Pair) (atoms : List (Ring.Poly Nat))
    (P : Ring.Poly Nat) (hR : 1≤R) (i : Fin 34) :
    copied C R cs atoms P (slots (i.castAdd 11))=ReusableArithmetic.natState C R [] P i := by
  rw [←right_words C R P]
  have old : before C R cs atoms P (slots (i.castAdd 11))=ReusableArithmetic.natState C R [] [] i := by
    simp only [slots,Fin.val_castAdd,dif_pos i.isLt,before,Fin.append,Fin.addCases_left]
    exact PacketAtoms.arithmetic_words C R id cs _ hR i
  by_cases h26:i=26
  · subst i;simp [copied,slots,PacketAtoms.arithmeticSlots,Function.update,Fin.ext_iff]
  by_cases h27:i=27
  · subst i;simp [copied,slots,PacketAtoms.arithmeticSlots,Function.update,Fin.ext_iff]
  have n26:slots (i.castAdd 11)≠26 := by
    intro he;apply h26
    have hv:=congrArg Fin.val he
    simp only [slots,Fin.val_castAdd,if_pos i.isLt,PacketAtoms.arithmeticSlots] at hv
    split_ifs at hv <;>apply Fin.ext <;>dsimp at hv <;>omega
  have n27:slots (i.castAdd 11)≠27 := by
    intro he;apply h27
    have hv:=congrArg Fin.val he
    simp only [slots,Fin.val_castAdd,if_pos i.isLt,PacketAtoms.arithmeticSlots] at hv
    split_ifs at hv <;>apply Fin.ext <;>dsimp at hv <;>omega
  simpa only [copied,Function.update_of_ne n26,Function.update_of_ne n27,
    Function.update_of_ne h26,Function.update_of_ne h27] using old

theorem packet_heads (i : Fin 45) : heads (slots i)=PacketRun.heads [] i := by
  fin_cases i <;>rfl

theorem packet_words (C R : Nat) (cs : List Pair) (atoms : List (Ring.Poly Nat))
    (P : Ring.Poly Nat) (hR : 1≤R) (i : Fin 45) :
    copied C R cs atoms P (slots i)=PacketRun.coldBank C R [] P (PacketRun.atomBank C R atoms) [] i := by
  refine Fin.addCases (m:=34) (n:=11) (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;>exact core_words C R cs atoms P hR _
  · fin_cases j
    · change AddressedAtomMaterialize.paddedA C R id cs (atoms.map (List.map (maskNat C))) 0 42=_
      exact PacketAtoms.dense_source C R id cs _
    all_goals rfl

theorem copy_run (C R : Nat) (cs : List Pair) (atoms : List (Ring.Poly Nat))
    (P : Ring.Poly Nat) (hR : 1≤R) (hP : PacketVector.Fits R (P.map (maskNat C))) :
    Step copy (4*R+5) heads (before C R cs atoms P) heads (copied C R cs atoms P) := by
  have ar (i : Fin 34) : before C R cs atoms P
      ((PacketAtoms.arithmeticSlots i).castAdd 12)=ReusableArithmetic.natState C R [] [] i := by
    simp only [before,Fin.append,Fin.addCases_left]
    exact PacketAtoms.arithmetic_words C R id cs _ hR i
  have width : before C R cs atoms P 33=UnaryTemplate.tape R := ar 31
  have len26 : (before C R cs atoms P 26).length=R := by
    have he : before C R cs atoms P 26=ReusableArithmetic.natState C R [] [] 26 := ar 26
    rw [he]
    change (ZeroPadding.pad R []).length=R
    simp [ZeroPadding.pad]
  have len27 : (before C R cs atoms P 27).length=R := by
    have he : before C R cs atoms P 27=ReusableArithmetic.natState C R [] [] 27 := ar 27
    rw [he]
    change (ZeroPadding.pad R [false]).length=R
    simp only [ZeroPadding.pad_length,List.length_singleton,Nat.max_eq_left hR]
  exact PhysicalCopyPair.run R 33 46 26 47 27 heads (before C R cs atoms P)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl width
    (PacketVector.payload_length hP) len26 (PacketVector.count_length hP) len27

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.PacketAtomsJoin
