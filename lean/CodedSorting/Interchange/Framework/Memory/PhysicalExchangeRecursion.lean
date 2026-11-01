import CodedSorting.Shared.Memory.PhysicalFileHandles
import CodedSorting.Interchange.Framework.Recursion.ExchangeFamily

/-! A file interpreter defined by recursion on depth. Each network level calls the same interpreter for its child exchanges. This module proves the resulting file transformation and the recurrence for its I/O count. 




-/
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace CodedSorting.PhysicalExchangeRecursion
open Circuit Address RecursiveExchange RecursiveExchangeCost
open PhysicalRecursiveExchange PhysicalFieldPacking PhysicalRecursiveAdapters
open PhysicalWholeLevel PhysicalRecursiveCost CoordinateLayoutBridge
noncomputable section

abbrev Result := File × ℕ
abbrev ScalarData (f P G S : ℕ) := FullAddress (Fin P) (Scalar f) (Fin G) (Fin S) → Bit

def volume (base k rows G S : ℕ) : ℕ :=
  ScalarVolume (base*Parameters.m^k) (rows*Parameters.W^k) G S

def leaf (f P G S cutoff B : ℕ) (source : File) : Option Result :=
  (BaseExchangeProgram.adaptiveRun (P := P) (Q := radix^f) (G := G) (S := S) cutoff B source).map
    (fun result => (result.output.finish,result.transfers))

def run (base cutoff B : ℕ) (hB : 0 < B) :
    (k rows G S : ℕ) → File → Option Result
  | 0,rows,G,S,source =>
      leaf (base*Parameters.m^0) (rows*Parameters.W^0) G S cutoff B source
  | k+1,rows,G,S,source =>
      if volume base (k+1) rows G S ≤ cutoff then
        leaf (base*Parameters.m^(k+1)) (rows*Parameters.W^(k+1)) G S cutoff B source
      else if hG : 0 < G then if hS : 0 < S then
        let f := base*Parameters.m^k
        let child : FileChild Unit := fun c file state =>
          (run base cutoff B hB k (rows*beforeCard f (childRow c))
            (childG f G c) (childS f S c) file).map
              (fun result => ⟨result.1,c,state,result.2⟩)
        (executeLevel f (rows*Parameters.W^k) G S B hG hS hB child source ()).map
          (fun out => (out.output,out.localCost+out.recursiveCost))
      else none else none

def runChildren (base cutoff B : ℕ) (hB : 0 < B) (k rows G S : ℕ) : FileChild Unit :=
  fun c file state =>
    (run base cutoff B hB k (rows*beforeCard (base*Parameters.m^k) (childRow c))
      (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c) file).map
        (fun result => ⟨result.1,c,state,result.2⟩)

def costBound (B cutoff : ℕ) : ℕ → ℕ → ℕ
  | 0,V => 12*(V/B+1)
  | k+1,V => if V ≤ cutoff then 12*(V/B+1) else
      max 12 levelCoefficient*(V/B+1)+Parameters.S*costBound B cutoff k (V/Parameters.W)

theorem leaf_cost_le_bound (B cutoff k V : ℕ) : 12*(V/B+1) ≤ costBound B cutoff k V := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
      unfold costBound
      split_ifs
      · exact le_rfl
      · exact (Nat.mul_le_mul_right _ (le_max_left _ _)).trans (Nat.le_add_right _ _)

theorem scaled_leaf_cost {B V cost : ℕ} (hB : 0 < B)
    (hc : cost*B ≤ 6*(V+B)) : cost ≤ 12*(V/B+1) := by
  have hmod := Nat.mod_lt V hB
  have hdiv := Nat.div_add_mod V B
  have hv : V ≤ (V/B+1)*B := by nlinarith
  have hb : B ≤ (V/B+1)*B := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hs : cost*B ≤ (12*(V/B+1))*B := by nlinarith
  exact Nat.le_of_mul_le_mul_right hs hB

theorem leaf_correct (f P G S cutoff B : ℕ) (hB : 0 < B)
    (F : ScalarData f P G S) (source : File)
    (hs : source=represented (scalarLayout f P G S) B hB F)
    (hstartup : cutoff < ScalarVolume f P G S →
      (radix^f*radix^f)*B ≤ ScalarVolume f P G S+B) :
    ∃ result, leaf f P G S cutoff B source=some result ∧
      result.1=represented (scalarLayout f P G S) B hB (transport exchangeEquiv F) ∧
      result.2 ≤ 12*(ScalarVolume f P G S/B+1) := by
  obtain ⟨result,hr,ho,_,hc⟩ := leaf_execution f P G S cutoff B hB F source hs hstartup
  exact ⟨(result.output.finish,result.transfers),by rw [leaf,hr]; rfl,ho,scaled_leaf_cost hB hc⟩

def childData (base k rows G S : ℕ) (c : Child)
    (F : EdgeStream (base*Parameters.m^k) (rows*Parameters.W^k) G S) :
    ScalarData (base*Parameters.m^k)
      ((rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k)
      (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c) :=
  (F ∘ (childScalarShape (base*Parameters.m^k) (rows*Parameters.W^k) G S c).symm) ∘
    (scalarPrefixShape _ _ _ _ _ (RecursiveCallShape.selected_prefix base k rows c)).symm

theorem child_file (base k rows G S B : ℕ) (hB : 0 < B) (c : Child)
    (F : EdgeStream (base*Parameters.m^k) (rows*Parameters.W^k) G S) :
    represented (scalarLayout (base*Parameters.m^k)
      ((rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k)
      (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c))
        B hB (childData base k rows G S c F) =
      represented (commonLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S) B hB F := by
  rw [childData,scalar_prefix_file,child_scalar_file]

theorem child_output_file (base k rows G S B : ℕ) (hB : 0 < B) (c : Child)
    (F : EdgeStream (base*Parameters.m^k) (rows*Parameters.W^k) G S) :
    represented (scalarLayout (base*Parameters.m^k)
      ((rows*beforeCard (base*Parameters.m^k) (childRow c))*Parameters.W^k)
      (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c))
        B hB (transport exchangeEquiv (childData base k rows G S c F)) =
      represented (commonLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S) B hB
        (transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F) := by
  rw [childData,scalar_prefix_output_file,child_scalar_output_file]

theorem child_volume_eq (base k rows G S : ℕ) (c : Child) :
    volume base k (rows*beforeCard (base*Parameters.m^k) (childRow c))
      (childG (base*Parameters.m^k) G c) (childS (base*Parameters.m^k) S c) =
        volume base (k+1) rows G S/Parameters.W := by
  have h := RecursiveCallShape.selected_scalar_volume base k rows G S c
  rw [RecursiveCallShape.selected_scalarCall] at h
  exact h

theorem child_gap_pos (f G : ℕ) (c : Child) (hG : 0 < G) : 0 < childG f G c := by
  letI : Nonempty (Fin G) := ⟨⟨0,hG⟩⟩
  exact Fintype.card_pos


/-- All recursive child contracts have been discharged by induction on the
actual file interpreter. Correctness and the I/O recurrence concern the
same successful return value. The only leaf premise is a single bound for
the globally fixed base field, not an oracle about every child call. -/
theorem run_correct_cost (base cutoff B : ℕ) (hB : 0 < B)
    (hbase : (radix^base*radix^base)*B ≤ cutoff+B)
    (k rows G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (F : ScalarData (base*Parameters.m^k) (rows*Parameters.W^k) G S)
    (source : File)
    (hs : source=represented (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S) B hB F) :
    ∃ result, run base cutoff B hB k rows G S source=some result ∧
      result.1=represented (scalarLayout (base*Parameters.m^k) (rows*Parameters.W^k) G S)
        B hB (transport exchangeEquiv F) ∧
      result.2 ≤ costBound B cutoff k (volume base k rows G S) := by
  induction k generalizing rows G S source with
  | zero =>
      have hb : (radix^(base*Parameters.m^0)*radix^(base*Parameters.m^0))*B ≤ cutoff+B := by
        simpa only [pow_zero,Nat.mul_one] using hbase
      obtain ⟨result,hr,ho,hc⟩ := leaf_correct (base*Parameters.m^0) (rows*Parameters.W^0)
        G S cutoff B hB F source hs
        (fun hcut => hb.trans (Nat.add_le_add_right (Nat.le_of_lt hcut) B))
      exact ⟨result,hr,ho,hc⟩
  | succ k ih =>
      by_cases hfit : volume base (k+1) rows G S ≤ cutoff
      · obtain ⟨result,hr,ho,hc⟩ := leaf_correct (base*Parameters.m^(k+1))
          (rows*Parameters.W^(k+1)) G S cutoff B hB F source hs
          (fun hcut => False.elim (by change cutoff < volume base (k+1) rows G S at hcut; omega))
        refine ⟨result,?_,ho,hc.trans (leaf_cost_le_bound B cutoff (k+1) _)⟩
        rw [run,if_pos hfit]
        exact hr
      · let f := base*Parameters.m^k
        let P := rows*Parameters.W^k
        let C := costBound B cutoff k (volume base (k+1) rows G S/Parameters.W)
        have child_success (c : Child) (data : EdgeStream f P G S) (state : Unit) (file : File)
            (hfile : file=represented (commonLayout f P G S) B hB data) :
            ∃ result, runChildren base cutoff B hB k rows G S c file state=some result ∧
              result.output=represented (commonLayout f P G S) B hB
                (transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) data) ∧
              result.returned=c ∧ result.state=state ∧ result.cost≤C := by
          obtain ⟨out,hr,ho,hc⟩ := ih
            (rows*beforeCard f (childRow c)) (childG f G c) (childS f S c)
            (child_gap_pos f G c hG) (childS_pos f S c hS)
            (childData base k rows G S c data) file
            (hfile.trans (child_file base k rows G S B hB c data).symm)
          refine ⟨⟨out.1,c,state,out.2⟩,?_,?_,rfl,rfl,?_⟩
          · change (run base cutoff B hB k _ _ _ file).map _ = _
            rw [hr]
            rfl
          · exact ho.trans (child_output_file base k rows G S B hB c data)
          · simpa only [C,f,child_volume_eq] using hc
        have havailable : ChildAvailable (actualLayouts f P G S hG hS).layout B hB
            (exchangeChild f P G S) (runChildren base cutoff B hB k rows G S) := by
          intro c data state file hfile
          obtain ⟨result,hr,ho,hret,hstate,hcost⟩ := child_success c data state file hfile
          exact ⟨result,⟨hfile,hr,ho,hret,hstate⟩⟩
        have hcost : ChildCostBound (actualLayouts f P G S hG hS) B hB
            (exchangeChild f P G S) (runChildren base cutoff B hB k rows G S) C := by
          intro c data state file result hr
          obtain ⟨out,hout,ho,hret,hstate,hbound⟩ := child_success c data state file hr.source_eq
          have he : out=result := Option.some.inj (hout.symm.trans hr.actual)
          simpa only [he] using hbound
        obtain ⟨out,hr,ho,hstate,hl,hrec⟩ := exchange_execution_cost f P G S B hG hS hB
          (runChildren base cutoff B hB k rows G S) C havailable hcost
          (parentData base k rows G S F) source ()
          (hs.trans (parent_file base k rows G S B hB F).symm)
        refine ⟨(out.output,out.localCost+out.recursiveCost),?_,?_,?_⟩
        · rw [run,if_neg hfit,dif_pos hG,dif_pos hS]
          change (executeLevel f P G S B hG hS hB
            (runChildren base cutoff B hB k rows G S) source ()).map _ = _
          rw [hr]
          rfl
        · exact ho.trans (parent_output_file base k rows G S B hB F)
        · change out.localCost+out.recursiveCost ≤ _
          have hl' : out.localCost ≤ levelCoefficient*(volume base (k+1) rows G S/B+1) := by
            simpa only [f,P,PhysicalRecursiveAdapters.parent_volume,volume] using hl
          rw [costBound,if_neg hfit]
          exact Nat.add_le_add
            (hl'.trans (Nat.mul_le_mul_right _ (le_max_right _ _))) hrec

end
end CodedSorting.PhysicalExchangeRecursion
