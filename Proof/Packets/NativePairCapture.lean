import Proof.CaseAnalysis.RowsRawPairCopy
import Proof.Rows.PhysicalFocusBoundary

/-! Copy the two actually resident polynomial halves of an atom pair to one
native stream, and pay for returning that stream cursor to zero. The pair
cache cursor advances, all work backing is reusable, and no result stream
is supplied as a machine parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairCapture
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word)

def selected (i : Fin 5) := decide (i=2)
noncomputable def machine := MaskedReset.machine CloseoutRowsRawPairCopy.machine selected
def heads (pos : Nat) : Fin 6→Nat := ![0,pos,0,0,0,0]
def data (R : Nat) (source out : List Bool) : Fin 6→List Bool :=
  ![List.replicate R false,source,ZeroPadding.pad R out,List.replicate R false,
    List.replicate R false,List.replicate (R+3) false]
def budget (p : Pair) := 2*CloseoutRowsRawPairCopy.budget p+2

theorem run (R : Nat) (pre post : List Bool) (p : Pair) (hR : 1≤R)
    (hcost : CloseoutRowsRawPairCopy.budget p≤R+3) :
    Step machine (budget p) (heads pre.length) (data R (pre++word p++post) [])
      (heads (pre.length+(word p).length))
      (data R (pre++word p++post) (ExtIncidence.stream (p.1++p.2))) := by
  have base:=CloseoutRowsRawPairCopy.copy_run R 0 [] pre post [] p hR
  have padded:=base.pad (![R,0,R,R,0] : Fin 5→Nat)
  have actual:=padded.mask selected (by intro i hi;fin_cases i <;> simp_all [selected,CloseoutRowsRawPolynomialAdd.heads]) hcost
  have one : ZeroPadding.pad R [false]=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  have one' : false::List.replicate (R-1) false=List.replicate R false := by
    rw [←List.replicate_succ]
    congr 1
    omega
  have hi : (Fin.addCases (m:=5) (n:=1) (motive:=fun _=>Nat)
      (CloseoutRowsRawPolynomialAdd.heads 0 pre.length []) (fun _=>0))=heads pre.length := by
    funext i;fin_cases i <;>rfl
  have ho : (Fin.addCases (m:=5) (n:=1) (motive:=fun _=>Nat)
      (fun i=>if selected i then 0 else
        CloseoutRowsRawPolynomialAdd.heads 0 (pre.length+(word p).length)
          ([]++ExtIncidence.stream (p.1++p.2)) i) (fun _=>0))=
      heads (pre.length+(word p).length) := by
    funext i;fin_cases i <;>rfl
  apply (actual.congr_in hi ?_).congr ho ?_
  · funext i;fin_cases i <;>simp [data,CloseoutRowsRawPolynomialAdd.data,Fin.addCases,one,ZeroPadding.pad,one']
  · funext i;fin_cases i <;>simp [data,CloseoutRowsRawPolynomialAdd.data,Fin.addCases,one,ZeroPadding.pad,one']

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairCapture
