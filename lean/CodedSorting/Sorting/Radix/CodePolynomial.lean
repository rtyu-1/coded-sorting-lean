import CodedSorting.Sorting.Radix.Program.Power
import CodedSorting.Sorting.Local.Framework.Program

/-! Fixed polynomial bounds for the actual finite instruction lists.
These coarse bounds reserve finite program-counter space; they do not
replace the sharper I/O bound for the same programs. The coefficient is
formed from the new Construction exchange rate through CommonLocalBudgetRate.K.
The actual local charge theorem bounds LocalBudget.budget, then the
same interval and chunk charges bound the node instruction lists. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CodedSorting.Construction.Sorting.CommonMSDCodePolynomial
open CommonSortingNormalization CommonRecordProgram CodedSorting.Construction.Sorting.CommonLocalBudgetRate
noncomputable section
attribute [local irreducible] CodedSorting.Construction.streamCount CodedSorting.Construction.ambientDimension

def rateConstant : ℕ :=
  ⌈22194000000*GlobalSortingBound.rateConstant K tau⌉₊+1
def leafConstant : ℕ := 2*rateConstant+60
def nodeConstant : ℕ := 2*rateConstant+200

theorem height_le_input (q : Configuration) : q.height≤q.N := by
  have := CommonLocalDescriptorBounds.height_scaled_le_input q
  omega

theorem block_le_input (q : Configuration) : q.block≤q.N :=
  (CodedSorting.Construction.Sorting.CommonLocalRecursion.block_le_height q).trans (height_le_input q)

theorem rate_constant_positive : 0<rateConstant := by unfold rateConstant;omega

theorem rate_linear (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q≤rateConstant*(q.N+1) := by
  have hb := CommonLeafProgram.block_positive q
  have hH := CommonMSDRadixLogBounds.height_two q
  have hHR : (0:ℝ)<q.height := by exact_mod_cast (show 0<q.height by omega)
  have hHN : (q.height:ℝ)≤q.N := by exact_mod_cast height_le_input q
  have ha := CodedSorting.Construction.ArbitraryLogRate.normalized_log_one q.height q.block hb hnormal
  have ha0 : 0<Real.log ((q.height:ℝ)/q.block) := by linarith
  have hlog : 0≤Real.log (q.height:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤q.height by omega))
  have hlogH := Real.log_le_sub_one_of_pos hHR
  have hr0 : 0≤Real.log (q.height:ℝ)/Real.log ((q.height:ℝ)/q.block) :=
    div_nonneg hlog ha0.le
  have hrH : Real.log (q.height:ℝ)/Real.log ((q.height:ℝ)/q.block)≤q.height := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  have ht : tau≤1 := by
    have he : (0:ℝ)<CodedSorting.Construction.epsilon := by exact_mod_cast CodedSorting.Construction.epsilon_pos
    unfold tau
    linarith
  have hp : (Real.log (q.height:ℝ)/Real.log ((q.height:ℝ)/q.block))^tau≤q.height := by
    by_cases hr : Real.log (q.height:ℝ)/Real.log ((q.height:ℝ)/q.block)≤1
    · exact (Real.rpow_le_one hr0 hr tau_nonneg).trans (by exact_mod_cast (show 1≤q.height by omega))
    · exact (Real.rpow_le_self_of_one_le (by linarith) ht).trans hrH
  have hc0 : 0≤22194000000*GlobalSortingBound.rateConstant K tau :=
    mul_nonneg (by norm_num) CodedSorting.Construction.Sorting.CommonMSDGlobalPower.rate_constant_nonneg
  have hc : 22194000000*GlobalSortingBound.rateConstant K tau≤(rateConstant:ℝ) := by
    have h := Nat.le_ceil (22194000000*GlobalSortingBound.rateConstant K tau)
    unfold rateConstant
    push_cast
    linarith
  have h := CodedSorting.Construction.Sorting.CommonMSDGlobalPower.local_power q ha
  have hpow := mul_le_mul_of_nonneg_left (show 1+
      (Real.log (q.height:ℝ)/Real.log ((q.height:ℝ)/q.block))^tau≤(q.N:ℝ)+1 by linarith) hc0
  have hceil := mul_le_mul_of_nonneg_right hc (show (0:ℝ)≤(q.N:ℝ)+1 by positivity)
  have hfinal : (CodedSorting.Construction.Sorting.CommonMSDSemanticCost.localRate q:ℝ)≤(rateConstant:ℝ)*((q.N:ℝ)+1) :=
    h.trans (hpow.trans hceil)
  exact_mod_cast hfinal

theorem block_count_le (q : Configuration) (n : ℕ) :
    PhysicalStreamCursor.blockCount q.block n≤n+q.block := by
  have hb := CommonLeafProgram.block_positive q
  have h := LocalSortingCost.blockCount_capacity q.block hb n
  change PhysicalStreamCursor.blockCount q.block n*q.block≤n+q.block at h
  have hmono := Nat.le_mul_of_pos_right (PhysicalStreamCursor.blockCount q.block n) hb
  omega

theorem record_blocks_le (q : Configuration) (n : ℕ) : recordBlocks q n≤3*n+q.block := by
  rw [CommonRecordEncoding.recordBlocks_eq_words]
  exact block_count_le q (3*n)

theorem local_budget (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hsize : n≤q.height^2) :
    CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n≤rateConstant*(q.N+1)*(n+q.block) := by
  have h := CodedSorting.Construction.Sorting.CommonMSDSemanticCost.actual_local_charge q hnormal n hsize
  have hb := CommonLeafProgram.block_positive q
  have hm := Nat.le_mul_of_pos_right (CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n) hb
  exact hm.trans (h.trans (Nat.mul_le_mul_right (n+q.block) (rate_linear q hnormal)))

theorem local_budget_input (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.N) (hsize : n≤q.height^2) :
    CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 n≤2*rateConstant*(q.N+1)^2 := by
  have h := local_budget q hnormal n hsize
  have hB := block_le_input q
  have hm := Nat.mul_le_mul_left (rateConstant*(q.N+1)) (show n+q.block≤2*(q.N+1) by omega)
  nlinarith only [h,hm]

theorem interval_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.N) (hsize : n≤q.height^2) :
    CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge q n≤leafConstant*(q.N+1)^2 := by
  have h := local_budget_input q hnormal n hn hsize
  have hr := record_blocks_le q n
  have hb := block_le_input q
  unfold CodedSorting.Construction.Sorting.CommonMSDIntervalLocal.charge leafConstant
  nlinarith only [h,hr,hb,hn]

theorem chunk_count_le (q : Configuration) (n : ℕ) (hn : n≤q.N) :
    CodedSorting.CommonMSDChunks.chunkCount q n≤q.N+1 := by
  have hp := CodedSorting.CommonMSDChunks.chunk_positive q
  have hm := Nat.mul_le_mul_left q.N (show 1≤CodedSorting.CommonMSDChunks.chunkSize q by omega)
  unfold CodedSorting.CommonMSDChunks.chunkCount PhysicalStreamCursor.blockCount
  apply Nat.div_le_of_le_mul
  have hs : n+CodedSorting.CommonMSDChunks.chunkSize q-1≤n+CodedSorting.CommonMSDChunks.chunkSize q := by omega
  nlinarith only [hs,hm,hn]

theorem chunk_budget (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block) :
    CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (CodedSorting.CommonMSDChunks.chunkSize q)≤2*rateConstant*(q.N+1)^3 := by
  have h := local_budget q hnormal (CodedSorting.CommonMSDChunks.chunkSize q) le_rfl
  have hH := Nat.pow_le_pow_left (height_le_input q) 2
  have hb := block_le_input q
  have hm := Nat.mul_le_mul_left (rateConstant*(q.N+1))
    (show CodedSorting.CommonMSDChunks.chunkSize q+q.block≤2*(q.N+1)^2 by
      unfold CodedSorting.CommonMSDChunks.chunkSize;nlinarith)
  nlinarith only [h,hm]

theorem chunks_charge (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.N) :
    CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n≤(2*rateConstant+100)*(q.N+1)^4 := by
  let X := q.N+1
  have hX : 1≤X := by dsimp [X];omega
  have hN : q.N≤X := by dsimp [X];omega
  have hB := (block_le_input q).trans hN
  have hH := (height_le_input q).trans hN
  have hR : CodedSorting.CommonMSDChunks.chunkSize q≤X^2 := Nat.pow_le_pow_left hH 2
  have hpad := CodedSorting.CommonMSDChunks.padded_size_le q n
  have hpad' : CodedSorting.CommonMSDChunks.paddedSize q n≤2*X^2 := by nlinarith
  have hp := record_blocks_le q (CodedSorting.CommonMSDChunks.paddedSize q n)
  have hr := record_blocks_le q (CodedSorting.CommonMSDChunks.chunkSize q)
  have hi := record_blocks_le q n
  have hp' : recordBlocks q (CodedSorting.CommonMSDChunks.paddedSize q n)≤7*X^2 := by nlinarith
  have hr' : recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q)≤4*X^2 := by nlinarith
  have hi' : recordBlocks q n≤4*X^2 := by nlinarith
  have hc := chunk_count_le q n hn
  change CodedSorting.CommonMSDChunks.chunkCount q n≤X at hc
  have hk := chunk_budget q hnormal
  change CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (CodedSorting.CommonMSDChunks.chunkSize q)≤2*rateConstant*X^3 at hk
  have hm := Nat.mul_le_mul hc (Nat.add_le_add hk (Nat.mul_le_mul_left 12 hr'))
  have h2 : X^2≤X^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : X^3≤X^4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold CodedSorting.Construction.Sorting.CommonMSDChunks.charge
  change 3*recordBlocks q (CodedSorting.CommonMSDChunks.paddedSize q n)+
    CodedSorting.CommonMSDChunks.chunkCount q n*
      (CodedSorting.Construction.Sorting.CommonLocalBudget.budget q 3 (CodedSorting.CommonMSDChunks.chunkSize q)+
        12*recordBlocks q (CodedSorting.CommonMSDChunks.chunkSize q))+
    3*recordBlocks q n≤(2*rateConstant+100)*X^4
  nlinarith only [hp',hi',hm,h2,h3]

theorem node_length (q : Configuration)
    (hnormal : PhysicalLeafParameters.minimumRatio CodedSorting.Construction.ExchangeSpecialization.radix 1 CodedSorting.Construction.streamCount≤q.height/q.block)
    (n : ℕ) (hn : n≤q.N) :
    CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound q n (CommonMSDParameters.radix q)≤nodeConstant*(q.N+1)^4 := by
  let X := q.N+1
  have hX : 1≤X := by dsimp [X];omega
  have hN : q.N≤X := by dsimp [X];omega
  have hB := (block_le_input q).trans hN
  have hH := (height_le_input q).trans hN
  have hc := chunk_count_le q n hn
  change CodedSorting.CommonMSDChunks.chunkCount q n≤X at hc
  have hrows := CommonMSDRowDirectoryBatch.rowBlocks_bound q (CommonMSDChunkRows.row q n)
    (List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n))
  rw [CommonMSDChunkRows.volume_eq,List.length_finRange] at hrows
  have hb := CommonLeafProgram.block_positive q
  have hr0 := Nat.le_mul_of_pos_right (CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
    (List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n))) hb
  have hbc := Nat.mul_le_mul hB hc
  have hr : CommonMSDRowDirectoryBatch.rowBlocks q (CommonMSDChunkRows.row q n)
      (List.finRange (CodedSorting.CommonMSDChunks.chunkCount q n))≤4*X^2 := by nlinarith
  have hd0 := block_count_le q ((CommonMSDParameters.radix q*2)*q.digits)
  change CommonMSDDirectory.blocks q (CommonMSDParameters.radix q)≤
    (CommonMSDParameters.radix q*2)*q.digits+q.block at hd0
  have hf := CommonMSDParameters.radix_fields q
  have hd : CommonMSDDirectory.blocks q (CommonMSDParameters.radix q)≤2*X := by omega
  have hm := Nat.mul_le_mul (show 2*CommonMSDDirectory.blocks q (CommonMSDParameters.radix q)+2≤6*X by omega) hc
  have hp := chunks_charge q hnormal n hn
  change CodedSorting.Construction.Sorting.CommonMSDChunks.charge q n≤(2*rateConstant+100)*X^4 at hp
  have h24 : X^2≤X^4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold CodedSorting.Construction.Sorting.CommonMSDNodePass.lengthBound nodeConstant
  change _≤(2*rateConstant+200)*X^4
  nlinarith only [hp,hr,hm,h24]

end
end CodedSorting.Construction.Sorting.CommonMSDCodePolynomial
