import CodedSorting.Sorting.Radix.ConcreteWorkspace

section DiskCapacity
/-! Explicit polynomial disk allocation.  The coefficient and input
threshold below depend only on the fixed workspace polynomial and the
fixed word-size coefficient; neither is defined from the input length.
The source file starts at block zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity
open CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CommonRecordProgram
open CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation
noncomputable section

def coefficient (C κ : ℕ) : ℕ := (κ+1)*(C+16)+5

def threshold (C D κ : ℕ) : ℕ := coefficient C κ*2^(D+1)

theorem recordBlocks_le (q : Configuration) (n : ℕ) : recordBlocks q n≤3*n := by
  rw [CommonRecordEncoding.recordBlocks_eq_words]
  exact AllocatedDirectoryXor.blockCount_le_records _ _
    (CommonLeafProgram.block_positive q)

theorem frameBlocks_le (q : Configuration) : CommonMSDStack.frameBlocks q≤q.N := by
  have h := AllocatedDirectoryXor.blockCount_le_records q.block q.digits
    (CommonLeafProgram.block_positive q)
  have hd := CommonMSDDirectoryBounds.digits_le_height q
  have hH := CommonLocalDescriptorBounds.height_scaled_le_input q
  change CommonMSDStack.frameBlocks q≤q.digits at h
  omega

/-- The actual recursion depth is at most the number of key bits. -/
theorem depth_le_word (q : Configuration) : CommonMSDRadixCost.depth q≤q.w := by
  apply (Nat.le_pow_iff_clog_le (by
    have := CommonMSDParameters.radix_two q
    omega : 1<CommonMSDParameters.radix q)).1
  exact Nat.pow_le_pow_left (CommonMSDParameters.radix_two q) q.w

/-- This bound expands the concrete per-depth allocation, including the
main file, every node arena, and every actual disk-stack frame. -/
theorem endAddress_polynomial (q : Configuration) (normal : Normalized q)
    (K L C D κ : ℕ) (hD : 1≤D)
    (hwork : workSize q normal q.N K≤C*(q.N+1)^D)
    (hlevel : L≤κ*q.N) :
    endAddress q normal q.N K L 0≤coefficient C κ*(q.N+1)^(D+1) := by
  have hr := recordBlocks_le q q.N
  have hf := frameBlocks_le q
  have hx : q.N+1≤(q.N+1)^D := by
    simpa using Nat.pow_le_pow_right (show 0<q.N+1 by omega) hD
  have hlevel' : L+1≤(κ+1)*(q.N+1) := by nlinarith
  have harena : 3*recordBlocks q q.N+workSize q normal q.N K+6+
      CommonMSDStack.frameBlocks q≤(C+16)*(q.N+1)^D := by
    nlinarith
  have hm := Nat.mul_le_mul hlevel' harena
  have hp : q.N+1≤(q.N+1)^(D+1) := by
    simpa using Nat.pow_le_pow_right (show 0<q.N+1 by omega)
      (show 1≤D+1 by omega)
  have hb : recordBlocks q q.N+2≤5*(q.N+1)^(D+1) := by omega
  calc
    endAddress q normal q.N K L 0 = recordBlocks q q.N+2+
        (L+1)*(3*recordBlocks q q.N+workSize q normal q.N K+6+
          CommonMSDStack.frameBlocks q) := by
      unfold endAddress stack arena arenaSpan
      ring
    _ ≤ 5*(q.N+1)^(D+1)+(κ+1)*(q.N+1)*((C+16)*(q.N+1)^D) :=
      Nat.add_le_add hb hm
    _ = coefficient C κ*(q.N+1)^(D+1) := by
      unfold coefficient
      rw [pow_succ]
      ring

/-- One extra fixed exponent absorbs both the coefficient and the shift
from N to N+1 once the explicit, input-independent threshold is met. -/
theorem absorb (N A d e : ℕ) (hN : 1≤N)
    (hthreshold : A*2^d≤N) (he : d+1≤e) :
    A*(N+1)^d≤N^e := by
  have hbase : N+1≤2*N := by omega
  calc
    A*(N+1)^d ≤ A*(2*N)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = (A*2^d)*N^d := by rw [mul_pow]; ring
    _ ≤ N*N^d := Nat.mul_le_mul_right _ hthreshold
    _ = N^(d+1) := by rw [pow_succ]; ring
    _ ≤ N^e := Nat.pow_le_pow_right (by omega) he

/-- Construct the actual allocation condition from a proved workspace
polynomial.  No end-address assumption remains in this constructor. -/
def capacity (q : Configuration) (normal : Normalized q)
    (K L C D κ : ℕ) (hD : 1≤D)
    (hwork : workSize q normal q.N K≤C*(q.N+1)^D)
    (hlevel : L≤κ*q.N)
    (hthreshold : threshold C D κ≤q.N) (he : D+2≤q.exponent) :
    Capacity q normal q.N K L 0 where
  input := le_rfl
  exponent := by omega
  disk := (endAddress_polynomial q normal K L C D κ hD hwork hlevel).trans
    (absorb q.N (coefficient C κ) (D+1) q.exponent (by have:=q.input_large; omega)
      hthreshold (by omega))

/-- The same constructor at the actual radix and complete key depth. -/
def sortingCapacity (q : Configuration) (normal : Normalized q)
    (C D κ : ℕ) (hD : 1≤D)
    (hwork : workSize q normal q.N (CommonMSDParameters.radix q)≤C*(q.N+1)^D)
    (hword : q.w≤κ*q.N)
    (hthreshold : threshold C D κ≤q.N) (he : D+2≤q.exponent) :
    Capacity q normal q.N (CommonMSDParameters.radix q) (CommonMSDRadixCost.depth q) 0 :=
  capacity q normal _ _ C D κ hD hwork ((depth_le_word q).trans hword) hthreshold he

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity
end DiskCapacity

section AllocatedCapacity
/-! A concrete disk-capacity constructor for the complete sorting run.
Its workspace coefficient is fixed by the finite coding construction;
the caller supplies neither a workspace estimate nor an end address. -/
set_option autoImplicit false
namespace CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity
open CommonSortingNormalization CodedSorting.Construction.RecursiveParameters CommonMSDParameters
noncomputable section

def workspaceCoefficient : ℕ := CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.coefficient

def diskThreshold (κ : ℕ) : ℕ :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.threshold workspaceCoefficient 5 κ

/-- Every file, node arena, directory, and suspended continuation fits
in the original N^exponent-block disk.  The threshold is independent of
N and the exponent requirement is the fixed number seven. -/
def capacity (q : Configuration) (normal : Normalized q) (κ : ℕ)
    (hw : q.w≤κ*q.N) (hthreshold : diskThreshold κ≤q.N)
    (he : 7≤q.exponent) :
    CodedSorting.Construction.Sorting.CommonMSDGlobalAllocation.Capacity q normal q.N (radix q)
      (CommonMSDRadixCost.depth q) 0 :=
  CodedSorting.Construction.Sorting.CommonMSDGlobalDiskCapacity.sortingCapacity q normal workspaceCoefficient 5 κ
    (by omega) (CodedSorting.Construction.Sorting.CommonMSDConcreteWorkspace.work_le q normal) hw hthreshold he

end
end CodedSorting.Construction.Sorting.CommonMSDGlobalAllocatedCapacity
end AllocatedCapacity
