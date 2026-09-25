import Proof.Packets.DeltaSplitCounters
import Proof.Packets.ScalarSeedInto
import Proof.Packets.ScalarCounterInto
import Proof.Packets.ScalarTwiceInto

/-! Actual capped/offset counters and five framed delta metadata scalars from
retained numeric masters. All binary-zero frames are physically allocated;
no metadata frame enters the initial bank. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaScalarFields
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (i : Fin 25) : Nat := if i=2 ∨ i=3 then 1 else 0
def cw (R n : Nat) := ZeroPadding.pad R (CompareMachine.word n)
def fw (R u n : Nat) := ZeroPadding.pad R (frame (SignedSortKey.binary u n))
def input (R u n w parent child : Nat) (i : Fin 25) : List Bool :=
  if i=0 then cw R n else if i=1 then cw R w else if i=2 then cw R parent
  else if i=3 then cw R child else if i=4 then cw R u else List.replicate R false
def splitData (R u n w parent child : Nat) :=
  Function.update (Function.update (input R u n w parent child) 5 (cw R (min n w))) 6 (cw R (n-w))
def splitSlots : Fin 5→Fin 25 := ![0,1,5,6,7]
def split := RecoveryFocus.machine splitSlots DeltaSplitCounters.returned

theorem split_run (R u n w parent child : Nat) (hr : n+2≤R) :
    Step split (2*n+6) heads (input R u n w parent child) heads (splitData R u n w parent child) := by
  apply PhysicalFocusBoundary.focus (DeltaSplitCounters.ready R n w hr) splitSlots (by decide)
    heads heads _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    have h5 : i≠5 := by intro he;exact away 2 he.symm
    have h6 : i≠6 := by intro he;exact away 3 he.symm
    exact ⟨rfl,by simp only [splitData,Function.update_of_ne h5,Function.update_of_ne h6]⟩

def seedOne (port : Fin 25) := ScalarSeedInto.zeroMachine port 13 4
def seedData1 (R u : Nat) (A : Fin 25→List Bool) := Function.update (A) 8 (fw R u 0)
def seedData2 (R u : Nat) (A : Fin 25→List Bool) := Function.update (seedData1 R u A) 9 (fw R u 0)
def seedData3 (R u : Nat) (A : Fin 25→List Bool) := Function.update (seedData2 R u A) 10 (fw R u 0)
def seedData4 (R u : Nat) (A : Fin 25→List Bool) := Function.update (seedData3 R u A) 11 (fw R u 0)
def seedData5 (R u : Nat) (A : Fin 25→List Bool) := Function.update (seedData4 R u A) 12 (fw R u 0)
def seed := (Composition.machine (Composition.machine (Composition.machine (Composition.machine (seedOne 8) (seedOne 9)) (seedOne 10)) (seedOne 11)) (seedOne 12))
def seedBudget (u : Nat) := 5*(ScalarCounterSeed.budget u+4)+4
theorem seed_run (R u : Nat) (A : Fin 25→List Bool)
    (h8 : A 8=List.replicate R false) (h9 : A 9=List.replicate R false)
    (h10 : A 10=List.replicate R false) (h11 : A 11=List.replicate R false)
    (h12 : A 12=List.replicate R false) (hl : A 13=List.replicate R false)
    (hu : A 4=cw R u) (hr : 2*u+1≤R) :
    Step seed (seedBudget u) heads A heads (seedData5 R u A) := by
  have h0:=ScalarSeedInto.zero_run u R (8 : Fin 25) 13 4 (by decide) heads A
    rfl rfl rfl (by simpa [Function.update] using h8)
    (by simpa [Function.update] using hl) (by simpa [Function.update,cw] using hu) hr
  have h1:=ScalarSeedInto.zero_run u R (9 : Fin 25) 13 4 (by decide) heads (seedData1 R u A)
    rfl rfl rfl (by simpa [seedData1,Function.update] using h9)
    (by simpa [seedData1,Function.update] using hl) (by simpa [seedData1,Function.update,cw] using hu) hr
  have h2:=ScalarSeedInto.zero_run u R (10 : Fin 25) 13 4 (by decide) heads (seedData2 R u A)
    rfl rfl rfl (by simpa [seedData1,seedData2,Function.update] using h10)
    (by simpa [seedData1,seedData2,Function.update] using hl) (by simpa [seedData1,seedData2,Function.update,cw] using hu) hr
  have h3:=ScalarSeedInto.zero_run u R (11 : Fin 25) 13 4 (by decide) heads (seedData3 R u A)
    rfl rfl rfl (by simpa [seedData1,seedData2,seedData3,Function.update] using h11)
    (by simpa [seedData1,seedData2,seedData3,Function.update] using hl) (by simpa [seedData1,seedData2,seedData3,Function.update,cw] using hu) hr
  have h4:=ScalarSeedInto.zero_run u R (12 : Fin 25) 13 4 (by decide) heads (seedData4 R u A)
    rfl rfl rfl (by simpa [seedData1,seedData2,seedData3,seedData4,Function.update] using h12)
    (by simpa [seedData1,seedData2,seedData3,seedData4,Function.update] using hl) (by simpa [seedData1,seedData2,seedData3,seedData4,Function.update,cw] using hu) hr
  have h:=(((h0.seq h1).seq h2).seq h3).seq h4
  have hf : ((((ScalarCounterSeed.budget u+4)+1+(ScalarCounterSeed.budget u+4))+1+(ScalarCounterSeed.budget u+4))+1+(ScalarCounterSeed.budget u+4))+1+(ScalarCounterSeed.budget u+4)=seedBudget u := by unfold seedBudget;omega
  rw [hf] at h
  exact h
def start (R u n w parent child : Nat) := seedData5 R u (splitData R u n w parent child)
def cap := ScalarCounterInto.zeroMachine (8 : Fin 25) 13 5
def parentScalar := ScalarCounterInto.machine (9 : Fin 25) 13 2
def childScalar := ScalarCounterInto.machine (10 : Fin 25) 13 3
def offset := ScalarCounterInto.zeroMachine (11 : Fin 25) 13 6
def width := ScalarTwiceInto.zeroMachine (12 : Fin 25) 13 1
def converted1 (R u n w parent child : Nat) := Function.update (start R u n w parent child) 8 (fw R u (min n w))
def converted2 (R u n w parent child : Nat) := Function.update (converted1 R u n w parent child) 9 (fw R u (parent))
def converted3 (R u n w parent child : Nat) := Function.update (converted2 R u n w parent child) 10 (fw R u (child))
def converted4 (R u n w parent child : Nat) := Function.update (converted3 R u n w parent child) 11 (fw R u (n-w))
def converted5 (R u n w parent child : Nat) := Function.update (converted4 R u n w parent child) 12 (fw R u (2*w))
def convert := (Composition.machine (Composition.machine (Composition.machine (Composition.machine cap parentScalar) childScalar) offset) width)
def convertBudget (u n w parent child : Nat) :=
  (ScalarFromCounter.budget u (min n w)+4)+ScalarFromCounter.budget u parent+
  ScalarFromCounter.budget u child+(ScalarFromCounter.budget u (n-w)+4)+(ScalarTwice.budget u w+4)+4

theorem convert_run (R u n w parent child : Nat)
    (hn : n<2^u) (hp : parent<2^u) (hc : child<2^u) (hw : 2*w<2^u) (hr : 2*u+1≤R) :
    Step convert (convertBudget u n w parent child) heads (start R u n w parent child)
      heads (converted5 R u n w parent child) := by
  have h0:=ScalarCounterInto.zero_run u 0 R (min n w) (8 : Fin 25) 13 5 (by decide) heads (start R u n w parent child)
    rfl rfl rfl (by simp [start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by omega) hr
  have h1:=ScalarCounterInto.run u 0 R (parent) (9 : Fin 25) 13 2 (by decide) heads (converted1 R u n w parent child)
    rfl rfl rfl (by simp [converted1,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (hp) hr
  have h2:=ScalarCounterInto.run u 0 R (child) (10 : Fin 25) 13 3 (by decide) heads (converted2 R u n w parent child)
    rfl rfl rfl (by simp [converted1,converted2,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (hc) hr
  have h3:=ScalarCounterInto.zero_run u 0 R (n-w) (11 : Fin 25) 13 6 (by decide) heads (converted3 R u n w parent child)
    rfl rfl rfl (by simp [converted1,converted2,converted3,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,converted3,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,converted3,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by omega) hr
  have h4:=ScalarTwiceInto.zero_run u 0 R (w) (12 : Fin 25) 13 1 (by decide) heads (converted4 R u n w parent child)
    rfl rfl rfl (by simp [converted1,converted2,converted3,converted4,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,converted3,converted4,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (by simp [converted1,converted2,converted3,converted4,start,seedData1,seedData2,seedData3,seedData4,seedData5,splitData,input,fw,cw,Function.update]) (hw) hr
  have h:=(((h0.seq h1).seq h2).seq h3).seq h4
  have hf : ((((ScalarFromCounter.budget u (min n w)+4)+1+ScalarFromCounter.budget u parent)+1+
      ScalarFromCounter.budget u child)+1+(ScalarFromCounter.budget u (n-w)+4))+1+
      (ScalarTwice.budget u w+4)=convertBudget u n w parent child := by unfold convertBudget;omega
  rw [hf] at h
  exact h

def machine := Composition.machine split (Composition.machine seed convert)
def budget (u n w parent child : Nat) := (2*n+6)+1+(seedBudget u+1+convertBudget u n w parent child)

theorem run (R u n w parent child : Nat)
    (hn : n<2^u) (hp : parent<2^u) (hc : child<2^u) (hw : 2*w<2^u)
    (hR : 2*u+1≤R) (hN : n+2≤R) :
    Step machine (budget u n w parent child) heads (input R u n w parent child)
      heads (converted5 R u n w parent child) := by
  have hs:=seed_run R u (splitData R u n w parent child)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hR
  exact (split_run R u n w parent child hN).seq (hs.seq (convert_run R u n w parent child hn hp hc hw hR))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaScalarFields
