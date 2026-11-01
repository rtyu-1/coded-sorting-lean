import CodedSorting.Interchange.Framework.Columns.Join
import CodedSorting.Shared.Memory.MarginTransform

section JoinRun
/-! The entire counted slab join runs in the common finite machine. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonColumnJoin
open WordControl CommonSortingNormalization PhysicalStreamCursor
open CommonLeafProgram (Slots Store RAM Disk Machine phase machine)
open CommonLeafBatchProgram (extendDisk)

theorem five_refines (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hl : cursor q z s<count q z s)
    (hs : source q z s+cursor q z s<q.N^q.exponent)
    (hf : address q z false s<q.N^q.exponent)
    (he : address q z true s<q.N^q.exponent)
    (hcap : cursor q z s+1<(2^q.w)^q.digits) :
    ∃ (t : Store q) (out : Disk q),
      run q z 5 (machine q s disk)=(machine q t out,5) ∧
      extendDisk q out=joinStep (width q z s) (source q z s) (target q z s)
        (cursor q z s) (extendDisk q disk) ∧
      cursor q z t=cursor q z s+1 ∧ phase q t=0 ∧
      Descriptor q z s t ∧ SameFrame q s t := by
  obtain ⟨t,hr,hp',hd,hframe,hc⟩ := five_steps q z s disk hp hl hs hf he
  refine ⟨t,_,hr,?_,by simpa only [Nat.mod_eq_of_lt hcap] using hc,hp',hd,hframe⟩
  have hf' : target q z s+first q.block (width q z s) (cursor q z s)<q.N^q.exponent := hf
  have he' : target q z s+last q.block (width q z s) (cursor q z s)<q.N^q.exponent := he
  have hinput : extendDisk q disk (source q z s+cursor q z s)=
      disk ⟨source q z s+cursor q z s,hs⟩ := by simp [extendDisk,hs]
  have hfirst : extendDisk q disk (target q z s+first q.block (width q z s) (cursor q z s))=
      disk ⟨target q z s+first q.block (width q z s) (cursor q z s),hf'⟩ := by simp [extendDisk,hf']
  rw [joinStep,hinput,hfirst]
  let f := merge (width q z s) (cursor q z s) (first q.block (width q z s) (cursor q z s))
    (disk ⟨source q z s+cursor q z s,hs⟩) (disk ⟨address q z false s,hf⟩)
  have hmiddle : (Function.update disk ⟨address q z false s,hf⟩ f) ⟨address q z true s,he⟩ =
      writeBlock (extendDisk q disk) (address q z false s) f (address q z true s) := by
    have h := congrFun (CommonExchangePolicy.extend_update q disk
      (⟨address q z false s,hf⟩ : Fin (q.N^q.exponent)) f) (address q z true s)
    simpa only [extendDisk,he,dif_pos] using h
  rw [CommonExchangePolicy.extend_update,CommonExchangePolicy.extend_update,hmiddle]
  rfl


theorem run_fives (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (left : ℕ) (hp : phase q s=0)
    (hlimit : cursor q z s+left≤count q z s)
    (hcap : cursor q z s+left<(2^q.w)^q.digits)
    (hs : source q z s+cursor q z s+left≤q.N^q.exponent)
    (hf : ∀ k,k<count q z s → target q z s+first q.block (width q z s) k<q.N^q.exponent)
    (he : ∀ k,k<count q z s → target q z s+last q.block (width q z s) k<q.N^q.exponent) :
    ∃ (t : Store q) (out : Disk q),
      run q z (5*left) (machine q s disk)=(machine q t out,5*left) ∧
      extendDisk q out=joinDisk (width q z s) (source q z s) (target q z s)
        (cursor q z s) left (extendDisk q disk) ∧
      cursor q z t=cursor q z s+left ∧ phase q t=0 ∧
      Descriptor q z s t ∧ SameFrame q s t := by
  induction left generalizing s disk with
  | zero =>
      exact ⟨s,disk,rfl,rfl,by omega,hp,⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | succ left ih =>
      have hl : cursor q z s<count q z s := by omega
      obtain ⟨next,nextDisk,hstep,hdisk,hcur,hphase,hdesc,hframe⟩ :=
        five_refines q z s disk hp hl (by omega) (hf _ hl) (he _ hl) (by omega)
      have hn : count q z next=count q z s := by
        simp only [count,stride,hdesc.2.2.1,hdesc.2.2.2]
      obtain ⟨t,out,hr,hout,hct,hpt,hdt,hft⟩ := ih next nextDisk hphase
        (by rw [hcur,hn]; omega) (by rw [hcur]; omega)
        (by rw [hdesc.1,hcur]; omega)
        (by simpa only [hn,hdesc.2.1,hdesc.2.2.1] using hf)
        (by simpa only [hn,hdesc.2.1,hdesc.2.2.1] using he)
      refine ⟨t,out,?_,?_,by omega,hpt,?_,?_⟩
      · rw [show 5*(left+1)=5+5*left by omega,run_add,hstep]
        dsimp only
        rw [hr]
      · rw [hout,hdesc.1,hdesc.2.1,hdesc.2.2.1,hcur,hdisk]
        rfl
      · exact ⟨hdt.1.trans hdesc.1,hdt.2.1.trans hdesc.2.1,
          hdt.2.2.1.trans hdesc.2.2.1,hdt.2.2.2.trans hdesc.2.2.2⟩
      · exact ⟨hft.1.trans hframe.1,hft.2.1.trans hframe.2.1,
          hft.2.2.1.trans hframe.2.2.1,hft.2.2.2.1.trans hframe.2.2.2.1,
          hft.2.2.2.2.1.trans hframe.2.2.2.2.1,hft.2.2.2.2.2.trans hframe.2.2.2.2.2⟩

theorem halt (q : Configuration) (z : Slots q) (s : Store q)
    (hp : phase q s=0) (hc : count q z s≤cursor q z s) : policy q z (pack s)=none := by
  simp [policy,hp,show ¬cursor q z s<count q z s by omega]

/-- Actual halt, exact five transfers per aligned source block, and complete
reference-disk equality belong to one execution of one fixed policy. -/
theorem complete_join_scan (q : Configuration) (z : Slots q) (s : Store q) (disk : Disk q)
    (hp : phase q s=0) (hc : cursor q z s=0)
    (hs : source q z s+count q z s≤q.N^q.exponent)
    (hf : ∀ k,k<count q z s → target q z s+first q.block (width q z s) k<q.N^q.exponent)
    (he : ∀ k,k<count q z s → target q z s+last q.block (width q z s) k<q.N^q.exponent) :
    ∃ (t : Store q) (out : Disk q),
      run q z (5*count q z s) (machine q s disk)=(machine q t out,5*count q z s) ∧
      policy q z (pack t)=none ∧
      extendDisk q out=joinDisk (width q z s) (source q z s) (target q z s)
        0 (count q z s) (extendDisk q disk) ∧
      Descriptor q z s t ∧ SameFrame q s t := by
  obtain ⟨t,out,hr,hd,hcur,hphase,hdesc,hframe⟩ :=
    run_fives q z s disk (count q z s) hp (by rw [hc]; omega)
      (by rw [hc,Nat.zero_add]; exact descriptor_capacity q _ (by omega))
      (by simpa only [hc,Nat.add_zero] using hs) hf he
  refine ⟨t,out,hr,halt q z t hphase ?_,by simpa only [hc] using hd,hdesc,hframe⟩
  rw [hcur,hc,Nat.zero_add]
  simp only [count,stride,hdesc.2.2.1,hdesc.2.2.2]
  exact Nat.le_refl _

end CodedSorting.CommonColumnJoin
end JoinRun

section JoinMath
/-! Word semantics of the physical read/modify/write column join. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonColumnJoin
open WordControl PhysicalStreamCursor

theorem stride_positive {B n : ℕ} (hB : 0<B) (hn : 0<n) : 0<blockCount B n := by
  exact (cursor_live_iff B n 0 hB).2 (by simpa using hn)

theorem chunk_bounds {B n k : ℕ} (hB : 0<B) (hn : 0<n) :
    k % blockCount B n * B < n ∧
    0 < useful B n k ∧
    start B n k + useful B n k ≤ (k / blockCount B n+1)*n := by
  have hs := stride_positive hB hn
  have hr := Nat.mod_lt k hs
  have hrn := (cursor_live_iff B n (k%blockCount B n) hB).1 hr
  have hp : 0<min B (n-k%blockCount B n*B) := Nat.lt_min.mpr ⟨hB,by omega⟩
  have hm := Nat.min_le_right B (n-k%blockCount B n*B)
  refine ⟨hrn,hp,?_⟩
  unfold start useful
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt hrn)
  nlinarith

theorem start_zero (B n : ℕ) : start B n 0=0 := by simp [start]

theorem start_step {B n : ℕ} (hB : 0<B) (hn : 0<n) (k : ℕ) :
    start B n (k+1)=start B n k+useful B n k := by
  let s := blockCount B n
  let c := k/s
  let r := k%s
  have hs : 0<s := stride_positive hB hn
  have hr : r<s := Nat.mod_lt _ hs
  have hk : k=c*s+r := by simpa [c,r,Nat.mul_comm] using (Nat.div_add_mod k s).symm
  have hrn : r*B<n := (cursor_live_iff B n r hB).1 hr
  by_cases hnext : r+1<s
  · have hx : (r+1)*B<n := (cursor_live_iff B n (r+1) hB).1 hnext
    have hu : useful B n k=B := by
      unfold useful
      apply Nat.min_eq_left
      change B≤n-r*B
      have hx' : r*B+B<n := by nlinarith
      omega
    have hk1 : k+1=c*s+(r+1) := by omega
    have hd : (k+1)/s=c := by rw [hk1,Nat.add_div_of_dvd_right (dvd_mul_left s c)]; simp [Nat.div_eq_of_lt hnext,hs.ne']
    have hm : (k+1)%s=r+1 := by rw [hk1,Nat.add_mod]; simp [Nat.mod_eq_of_lt hnext]
    rw [hu]
    change (k+1)/s*n+(k+1)%s*B=k/s*n+k%s*B+B
    rw [hd,hm]
    dsimp [c,r]
    ring
  · have hre : r+1=s := by omega
    have hx : n≤(r+1)*B := by
      by_contra hh
      have hh' : (r+1)*B<n := Nat.lt_of_not_ge hh
      have ht := (cursor_live_iff B n (r+1) hB).2 hh'
      change r+1<s at ht
      omega
    have hu : useful B n k=n-r*B := by
      unfold useful
      apply Nat.min_eq_right
      change n-r*B≤B
      have hx' : n≤r*B+B := by nlinarith
      omega
    have hk1 : k+1=(c+1)*s := by nlinarith
    have hd : (k+1)/s=c+1 := by rw [hk1]; simp [hs.ne']
    have hm : (k+1)%s=0 := by rw [hk1]; simp
    rw [hu]
    change (k+1)/s*n+(k+1)%s*B=k/s*n+k%s*B+(n-r*B)
    rw [hd,hm]
    change (c+1)*n+0*B=c*n+r*B+(n-r*B)
    have hsub := Nat.sub_add_cancel (Nat.le_of_lt hrn)
    nlinarith

theorem start_mono {B n : ℕ} (hB : 0<B) (hn : 0<n) : Monotone (start B n) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [start_step hB hn]
  omega

theorem start_columns {B n : ℕ} (hB : 0<B) (hn : 0<n) (C : ℕ) :
    start B n (C*blockCount B n)=C*n := by
  have hs := stride_positive hB hn
  simp [start,Nat.mul_div_cancel,hs.ne']

theorem endpoint_bounds {B n C k : ℕ} (hB : 0<B)
    (hk : k<C*blockCount B n) :
    first B n k<blockCount B (C*n) ∧ last B n k<blockCount B (C*n) := by
  have hn : 0<n := by
    by_contra h
    have : n=0 := by omega
    subst n
    have : blockCount B 0=0 := by unfold blockCount; exact Nat.div_eq_of_lt (by omega)
    simp [this] at hk
  have hend : start B n k+useful B n k≤C*n := by
    rw [←start_step hB hn,←start_columns hB hn C]
    exact start_mono hB hn (by omega)
  have hu := (chunk_bounds hB hn (k:=k)).2.1
  constructor
  · apply (cursor_live_iff B (C*n) (first B n k) hB).2
    have hd := Nat.div_mul_le_self (start B n k) B
    unfold first
    omega
  · apply (cursor_live_iff B (C*n) (last B n k) hB).2
    have hd := Nat.div_mul_le_self (start B n k+useful B n k-1) B
    unfold last
    omega

/-- Every word of a chunk lies in one of its two endpoint blocks. -/
theorem chunk_block {B n k r : ℕ} (hB : 0<B)
    (hl : start B n k≤r) (hr : r<start B n k+useful B n k) :
    r/B=first B n k ∨ r/B=last B n k := by
  have hu : useful B n k≤B := Nat.min_le_left _ _
  have hlo := Nat.div_le_div_right (c:=B) hl
  have hhi := Nat.div_le_div_right (c:=B) (show r≤start B n k+useful B n k-1 by omega)
  have ha := Nat.mod_lt (start B n k) hB
  have he := Nat.mod_add_div (start B n k) B
  have hd := Nat.mod_add_div (start B n k+useful B n k-1) B
  have hb := Nat.mod_lt (start B n k+useful B n k-1) hB
  have hgap : (start B n k+useful B n k-1)/B≤start B n k/B+1 := by
    by_contra h
    have hx : start B n k/B+2≤(start B n k+useful B n k-1)/B := by omega
    have hmul := Nat.mul_le_mul_left B hx
    have hsub : start B n k+useful B n k-1+1=start B n k+useful B n k := by omega
    simp only [Nat.mul_add,Nat.mul_two] at hmul
    omega
  unfold first last
  omega

/-- A word is addressed relative to the first output block. -/
def outputWord {B w : ℕ} (hB : 0<B) (disk : ℕ→Words B w) (target r : ℕ) : Word w :=
  disk (target+r/B) ⟨r%B,Nat.mod_lt _ hB⟩

 theorem joinStep_word {B w n source target k r : ℕ} (hB : 0<B)
    (disk : ℕ→Words B w) :
    outputWord hB (joinStep n source target k disk) target r =
      if h : start B n k≤r ∧ r<start B n k+useful B n k then
        disk (source+k) ⟨r-start B n k,by have:=Nat.min_le_left B (n-k%blockCount B n*B); unfold useful at h; omega⟩
      else outputWord hB disk target r := by
  have hrmod := Nat.mod_lt r hB
  have hrdecomp : r/B*B+r%B=r := by simpa [Nat.mul_comm] using Nat.div_add_mod r B
  have hmerge (j : ℕ) (hj : r/B=j) (input old : Words B w) :
      merge n k j input old ⟨r%B,hrmod⟩ =
        if h : start B n k≤r ∧ r<start B n k+useful B n k then
          input ⟨r-start B n k,by have:=Nat.min_le_left B (n-k%blockCount B n*B); unfold useful at h; omega⟩
        else old ⟨r%B,hrmod⟩ := by
    have hd : j*B+r%B=r := by rw [←hj]; exact hrdecomp
    simp only [merge,hd]
  unfold outputWord joinStep writeBlock
  dsimp only
  simp only [Nat.add_left_cancel_iff]
  by_cases hl : r/B=last B n k
  · simp only [hl,↓reduceIte]
    rw [hmerge _ hl]
    split_ifs with h hf
    · rfl
    · rw [hmerge _ (hl.trans hf)]
      simp only [dif_neg h]
      rw [hf]
    · rfl
  · simp only [hl,↓reduceIte]
    by_cases hf : r/B=first B n k
    · simp only [hf,↓reduceIte]
      exact hmerge _ hf _ _
    · simp only [hf,↓reduceIte]
      have h : ¬(start B n k≤r ∧ r<start B n k+useful B n k) := by
        intro h
        rcases chunk_block hB h.1 h.2 with h|h
        · exact hf h
        · exact hl h
      simp only [dif_neg h]

 theorem joinStep_outside {B w n source target k j : ℕ} (disk : ℕ→Words B w)
    (hf : j≠target+first B n k) (hl : j≠target+last B n k) :
    joinStep n source target k disk j=disk j := by
  simp [joinStep,writeBlock,hf,hl]

/-- The two regions of block addresses are disjoint. -/
def Separated (source count target size : ℕ) : Prop :=
  source+count≤target ∨ target+size≤source

 theorem joinStep_source {B w n C source target k j : ℕ} (hB : 0<B)
    (hk : k<C*blockCount B n) (hj : j<C*blockCount B n)
    (hsep : Separated source (C*blockCount B n) target (blockCount B (C*n)))
    (disk : ℕ→Words B w) :
    joinStep n source target k disk (source+j)=disk (source+j) := by
  obtain ⟨hf,hl⟩ := endpoint_bounds hB hk
  apply joinStep_outside
  · rcases hsep with h|h <;> omega
  · rcases hsep with h|h <;> omega

/-- Later chunks do not disturb any word preceding their first word. -/
 theorem joinDisk_earlier {B w n source target k r : ℕ} (hB : 0<B) (hn : 0<n)
    (hr : r<start B n k) (left : ℕ) (disk : ℕ→Words B w) :
    outputWord hB (joinDisk n source target k left disk) target r=
      outputWord hB disk target r := by
  induction left generalizing k disk with
  | zero => rfl
  | succ left ih =>
    rw [joinDisk,ih]
    · rw [joinStep_word]
      simp only [dif_neg (show ¬(start B n k≤r ∧ r<start B n k+useful B n k) by omega)]
    · have hm := start_mono hB hn (show k≤k+1 by omega)
      omega

/-- Each useful source word is written exactly once and survives the rest
of the join, even when consecutive chunks share an output block. -/
 theorem joinDisk_chunk {B w n C source target : ℕ} (hB : 0<B) (hn : 0<n)
    (hsep : Separated source (C*blockCount B n) target (blockCount B (C*n)))
    (k left : ℕ) (hbound : k+left≤C*blockCount B n)
    (disk : ℕ→Words B w) (j : ℕ) (hjk : k≤j) (hjl : j<k+left)
    (i : Fin B) (hi : i.val<useful B n j) :
    outputWord hB (joinDisk n source target k left disk) target (start B n j+i.val)=
      disk (source+j) i := by
  induction left generalizing k disk with
  | zero => omega
  | succ left ih =>
    rw [joinDisk]
    by_cases hj : j=k
    · subst j
      rw [joinDisk_earlier hB hn]
      · rw [joinStep_word]
        have h : start B n k≤start B n k+i.val ∧
            start B n k+i.val<start B n k+useful B n k := by omega
        simp only [dif_pos h,Nat.add_sub_cancel_left]
      · rw [start_step hB hn]
        omega
    · rw [ih (k+1) (by omega) _ (by omega) (by omega)]
      exact congrFun (joinStep_source hB (by omega) (by omega) hsep disk) i

 theorem packed_chunk_index {B n c i : ℕ} (hB : 0<B) (hi : i<n) :
    let k := c*blockCount B n+i/B
    start B n k+i%B=c*n+i ∧ i%B<useful B n k ∧ i/B<blockCount B n := by
  have hn : 0<n := by omega
  have hs := stride_positive hB hn
  have hid := Nat.div_mul_le_self i B
  have hil : i/B<blockCount B n := (cursor_live_iff B n (i/B) hB).2 (by omega)
  have hdiv : (c*blockCount B n+i/B)/blockCount B n=c := by
    rw [Nat.add_div_of_dvd_right (dvd_mul_left (blockCount B n) c)]
    simp [hs.ne',Nat.div_eq_of_lt hil]
  have hmod : (c*blockCount B n+i/B)%blockCount B n=i/B := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hil]
  have hdecomp : i/B*B+i%B=i := by simpa [Nat.mul_comm] using Nat.div_add_mod i B
  dsimp only
  refine ⟨?_,?_,hil⟩
  · simp only [start,hdiv,hmod]
    omega
  · simp only [useful,hmod]
    exact Nat.lt_min.mpr ⟨Nat.mod_lt i hB,by omega⟩

/-- The complete physical join removes slab padding and concatenates all
columns in column order. The final partially filled block is not constrained
beyond the declared word count. -/
 theorem joinDisk_packed {B w n C source target : ℕ} (hB : 0<B)
    (hsep : Separated source (C*blockCount B n) target (blockCount B (C*n)))
    (disk : ℕ→Words B w) (c i : ℕ) (hc : c<C) (hi : i<n) :
    outputWord hB (joinDisk n source target 0 (C*blockCount B n) disk) target (c*n+i)=
      disk (source+c*blockCount B n+i/B) ⟨i%B,Nat.mod_lt _ hB⟩ := by
  have hn : 0<n := by omega
  obtain ⟨he,hu,hix⟩ := packed_chunk_index (c:=c) hB hi
  have hj : c*blockCount B n+i/B<C*blockCount B n := by
    have hmul := Nat.mul_le_mul_right (blockCount B n) (show c+1≤C by omega)
    nlinarith
  have h := joinDisk_chunk hB hn hsep 0 (C*blockCount B n) (by omega) disk
    (c*blockCount B n+i/B) (Nat.zero_le _) (by simpa only [Nat.zero_add] using hj) ⟨i%B,Nat.mod_lt _ hB⟩ hu
  simpa only [he,Nat.add_assoc] using h

 theorem joinDisk_outside {B w n C source target : ℕ} (hB : 0<B)
    (k left : ℕ) (hbound : k+left≤C*blockCount B n)
    (disk : ℕ→Words B w) (j : ℕ)
    (hj : j<target ∨ target+blockCount B (C*n)≤j) :
    joinDisk n source target k left disk j=disk j := by
  induction left generalizing k disk with
  | zero => rfl
  | succ left ih =>
    rw [joinDisk,ih (k+1) (by omega)]
    obtain ⟨hf,hl⟩ := endpoint_bounds (n:=n) (C:=C) (k:=k) hB (by omega)
    apply joinStep_outside
    · rcases hj with h|h <;> omega
    · rcases hj with h|h <;> omega

/-- Above the leaf threshold, slab rounding changes a scan bound by at
most a factor of two. Small columns use the shared-buffer leaf batch. -/
 theorem slab_blocks_le_scan {B n C : ℕ} (hB : 0<B) (hn : B≤n) :
    C*blockCount B n≤2*blockCount B (C*n) := by
  have hfloor := Nat.div_mul_le_self (n+B-1) B
  change blockCount B n*B≤n+B-1 at hfloor
  have hnB : 0<n+B := by omega
  have hsub : n+B-1+1=n+B := by omega
  have hsmall : blockCount B n*B≤2*n := by omega
  have hscaled := Nat.mul_le_mul_left C hsmall
  have hcover : C*n≤blockCount B (C*n)*B := by
    by_contra h
    have ht := (cursor_live_iff B (C*n) (blockCount B (C*n)) hB).2 (Nat.lt_of_not_ge h)
    exact (Nat.lt_irrefl _) ht
  have htarget := Nat.mul_le_mul_left 2 hcover
  have hcancel : (C*blockCount B n)*B≤(2*blockCount B (C*n))*B := by nlinarith
  exact Nat.le_of_mul_le_mul_right hcancel hB

 theorem join_scan_cost {B n C : ℕ} (hB : 0<B) (hn : B≤n) :
    5*(C*blockCount B n)≤10*blockCount B (C*n) := by
  have := slab_blocks_le_scan (C:=C) hB hn
  omega

end CodedSorting.CommonColumnJoin
end JoinMath

section JoinEndpoint
/-! Resident initialization and counted-column join on one finite machine. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace CodedSorting.CommonColumnJoin
open WordControl CommonSortingNormalization PhysicalStreamCursor
open CommonLeafProgram (Slots Store RAM Disk Machine phase setPhase machine)
open CommonLeafBatchProgram (extendDisk)

def initialStore (q : Configuration) (z : Slots q)
    (n C : Fin (q.N^q.exponent+1)) (a b : Fin (q.N^q.exponent)) (s : Store q) : Store q :=
  setPhase q 0 {s with
    readers:=Function.update s.readers z.reader
      ⟨encodeNat q.digits q.w a.val,encodeNat q.digits q.w n.val,
        Fin.append (Fin.append s.transfer (encodeNat q.digits q.w C.val))
          (encodeNat q.digits q.w 0)⟩
    writers:=Function.update s.writers z.writer
      {(s.writers z.writer) with base:=encodeNat q.digits q.w b.val}}

@[simp] theorem lengthWords_append (B d w : ℕ) (a : Words B w) (b c : Words d w) :
    S.lengthWords (Fin.append (Fin.append a b) c)=b := by
  funext i
  simp [S.lengthWords]
@[simp] theorem cursorWords_append (B d w : ℕ) (a : Words B w) (b c : Words d w) :
    S.cursorWords (Fin.append (Fin.append a b) c)=c := by
  funext i
  simp [S.cursorWords]

theorem initial_fields (q : Configuration) (z : Slots q)
    (n C : Fin (q.N^q.exponent+1)) (a b : Fin (q.N^q.exponent)) (s : Store q) :
    phase q (initialStore q z n C a b s)=0 ∧
    cursor q z (initialStore q z n C a b s)=0 ∧
    source q z (initialStore q z n C a b s)=a.val ∧
    target q z (initialStore q z n C a b s)=b.val ∧
    width q z (initialStore q z n C a b s)=n.val ∧
    columns q z (initialStore q z n C a b s)=C.val := by
  have ha := descriptor_capacity q a.val a.isLt.le
  have hb := descriptor_capacity q b.val b.isLt.le
  have hn := descriptor_capacity q n.val (by have:=n.isLt; omega)
  have hC := descriptor_capacity q C.val (by have:=C.isLt; omega)
  have hz : 0<(2^q.w)^q.digits := by positivity
  refine ⟨CommonLeafProgram.phase_setPhase q 0 _ (by positivity),?_,?_,?_,?_,?_⟩
  all_goals simp only [cursor,source,target,width,columns,initialStore,setPhase,Function.update_self,
    lengthWords_append,cursorWords_append,decodeNat_encode _ _ _ ha,decodeNat_encode _ _ _ hb,
    decodeNat_encode _ _ _ hn,decodeNat_encode _ _ _ hC,decodeNat_encode _ _ _ hz]

theorem initialized_scan (q : Configuration) (z : Slots q)
    (n C : Fin (q.N^q.exponent+1)) (a b : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hs : a.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (ht : b.val+blockCount q.block (C.val*n.val)≤q.N^q.exponent) :
    ∃ (t : Store q) (out : Disk q),
      run q z (5*(C.val*blockCount q.block n.val))
        (machine q (initialStore q z n C a b s) disk)=
          (machine q t out,5*(C.val*blockCount q.block n.val)) ∧
      policy q z (pack t)=none ∧
      extendDisk q out=joinDisk n.val a.val b.val 0
        (C.val*blockCount q.block n.val) (extendDisk q disk) ∧
      Descriptor q z (initialStore q z n C a b s) t ∧
      SameFrame q (initialStore q z n C a b s) t := by
  obtain ⟨hp,hc,ha,hb,hn,hC⟩ := initial_fields q z n C a b s
  have hcount : count q z (initialStore q z n C a b s)=C.val*blockCount q.block n.val := by
    simp only [count,stride,hn,hC]
  obtain ⟨t,out,hr,hh,hd,hdesc,hframe⟩ := complete_join_scan q z
    (initialStore q z n C a b s) disk hp hc (by simpa only [ha,hcount] using hs)
    (by
      intro k hk
      rw [hcount] at hk
      rw [hb,hn]
      have he := (endpoint_bounds (CommonLeafProgram.block_positive q) hk).1
      omega)
    (by
      intro k hk
      rw [hcount] at hk
      rw [hb,hn]
      have he := (endpoint_bounds (CommonLeafProgram.block_positive q) hk).2
      omega)
  exact ⟨t,out,by simpa only [hcount] using hr,hh,
    by simpa only [hn,ha,hb,hcount] using hd,hdesc,hframe⟩

/-- A whole real scan: columns in independently aligned slabs become the
packed concatenation, with the same run proving output, halt and cost. -/
theorem join_columns_policy_refines (q : Configuration) (z : Slots q)
    (n C : Fin (q.N^q.exponent+1)) (a b : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hs : a.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (ht : b.val+blockCount q.block (C.val*n.val)≤q.N^q.exponent)
    (hsep : Separated a.val (C.val*blockCount q.block n.val) b.val
      (blockCount q.block (C.val*n.val))) :
    ∃ (t : Store q) (out : Disk q),
      run q z (5*(C.val*blockCount q.block n.val))
        (machine q (initialStore q z n C a b s) disk)=
          (machine q t out,5*(C.val*blockCount q.block n.val)) ∧
      policy q z (pack t)=none ∧
      (∀ c i,c<C.val → i<n.val →
        outputWord (CommonLeafProgram.block_positive q) (extendDisk q out) b.val (c*n.val+i)=
          extendDisk q disk (a.val+c*blockCount q.block n.val+i/q.block)
            ⟨i%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩) ∧
      (∀ j : Fin (q.N^q.exponent),j.val<b.val ∨
        b.val+blockCount q.block (C.val*n.val)≤j.val → out j=disk j) ∧
      t.leaf=s.leaf ∧ t.directories=s.directories ∧ t.shapes=s.shapes ∧
      t.top=s.top ∧ t.pcs=s.pcs ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨t,out,hr,hh,hd,_,hf⟩ := initialized_scan q z n C a b s disk hs ht
  refine ⟨t,out,hr,hh,?_,?_,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,resident_memory q⟩
  · intro c i hc hi
    rw [hd]
    exact joinDisk_packed (CommonLeafProgram.block_positive q) hsep _ c i hc hi
  · intro j hj
    have h := congrFun hd j.val
    rw [joinDisk_outside (n:=n.val) (C:=C.val) (CommonLeafProgram.block_positive q)
      0 (C.val*blockCount q.block n.val) (by omega) (extendDisk q disk) j.val hj] at h
    simpa only [extendDisk,dif_pos j.isLt] using h

end CodedSorting.CommonColumnJoin
end JoinEndpoint

section Split
/-! Actual splitting of a packed word stream into equal-length,
block-aligned column slabs. Width and column count are decoded from an
existing shape bank; no column-file list or payload-dependent code is
resident. Every slab block is assembled by two real reads and one write.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CodedSorting.CommonColumnSplit
open WordControl CommonSortingNormalization CommonMarginGather PhysicalStreamCursor
open CommonLeafProgram (Slots Store Disk phase inputCursor sourceBase targetBase machine)
open CommonColumnJoin (start useful first last)

def width (q : Configuration) (s : Shape q) := CommonMarginTransform.field q s 0
def columns (q : Configuration) (s : Shape q) := CommonMarginTransform.field q s 1
def stride (q : Configuration) (s : Shape q) := blockCount q.block (width q s)
def count (q : Configuration) (s : Shape q) := columns q s*stride q s

def address (q : Configuration) (source a : ℕ) : Fin (q.N^q.exponent) :=
  if h : source+a<q.N^q.exponent then ⟨source+a,h⟩
  else ⟨0,pow_pos (by have:=q.input_large; omega) _⟩

def assemble (q : Configuration) (s : Shape q) (k : ℕ)
    (a b : Words q.block q.w) : Words q.block q.w := fun i =>
  if i.val<useful q.block (width q s) k then
    let r := start q.block (width q s) k+i.val
    let j : Fin q.block := ⟨r%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩
    if r/q.block=first q.block (width q s) k then a j else b j
  else 0

def scheme (q : Configuration) : Scheme q where
  count := count q
  first s source k := address q source (first q.block (width q s) k)
  second s source k := address q source (last q.block (width q s) k)
  assemble := assemble q

@[simp] theorem address_val (q : Configuration) (source a : ℕ)
    (h : source+a<q.N^q.exponent) : (address q source a).val=source+a := by
  simp only [address,dif_pos h]

theorem reads_outside (q : Configuration) (s : Shape q) (source target : ℕ)
    (hfit : source+blockCount q.block (columns q s*width q s)≤q.N^q.exponent)
    (hsep : source+blockCount q.block (columns q s*width q s)≤target ∨
      target+count q s≤source) : ReadsOutside q (scheme q) s source target := by
  intro k hk
  have he := CommonColumnJoin.endpoint_bounds (CommonLeafProgram.block_positive q) hk
  have ha : source+first q.block (width q s) k<q.N^q.exponent := by omega
  have hb : source+last q.block (width q s) k<q.N^q.exponent := by omega
  simp only [scheme,address_val q source _ ha,address_val q source _ hb]
  rcases hsep with h|h
  · exact ⟨Or.inl (by omega),Or.inl (by omega)⟩
  · exact ⟨Or.inr (by omega),Or.inr (by omega)⟩

theorem spec_word (q : Configuration) (s : Shape q) (source k : ℕ)
    (disk : Disk q) (i : Fin q.block) (hi : i.val<useful q.block (width q s) k) :
    specBlock q (scheme q) s source k disk i=
      disk (address q source ((start q.block (width q s) k+i.val)/q.block))
        ⟨(start q.block (width q s) k+i.val)%q.block,
          Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ := by
  have h := CommonColumnJoin.chunk_block (CommonLeafProgram.block_positive q)
    (Nat.le_add_right (start q.block (width q s) k) i.val)
    (show start q.block (width q s) k+i.val<start q.block (width q s) k+useful q.block (width q s) k by omega)
  simp only [specBlock,scheme,assemble,hi,↓reduceIte]
  rcases h with h|h
  · simp only [h,↓reduceIte]
  · by_cases he : (start q.block (width q s) k+i.val)/q.block=first q.block (width q s) k
    · simp only [he,↓reduceIte]
    · have he' : last q.block (width q s) k≠first q.block (width q s) k := by omega
      simp only [h,he',↓reduceIte]

/-- Identify a live word inside its unique column slab block. -/
theorem column_position (B n C c j : ℕ) (hB : 0<B) (hc : c<C) (hj : j<n) :
    let k := c*blockCount B n+j/B
    k<C*blockCount B n ∧ j%B<useful B n k ∧ start B n k+j%B=c*n+j := by
  have hn : 0<n := by omega
  have hs := CommonColumnJoin.stride_positive hB hn
  have hjb : j/B<blockCount B n := by
    apply (cursor_live_iff B n (j/B) hB).2
    exact (Nat.div_mul_le_self j B).trans_lt hj
  have hd : (c*blockCount B n+j/B)/blockCount B n=c := by
    rw [Nat.mul_comm c (blockCount B n),Nat.mul_add_div hs,Nat.div_eq_of_lt hjb,Nat.add_zero]
  have hm : (c*blockCount B n+j/B)%blockCount B n=j/B := by
    exact Nat.mul_add_mod_of_lt hjb
  have hjm := Nat.mod_lt j hB
  have he := Nat.div_add_mod j B
  rw [Nat.mul_comm B (j/B)] at he
  dsimp only
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · simp only [useful,hm]
    exact Nat.lt_min.mpr ⟨hjm,by omega⟩
  · simp only [start,hd,hm]
    omega

/-- Same actual run, exact charge, halt and every column word at its
explicit aligned slab address. Padding words are not treated as payload. -/
theorem complete (q : Configuration) (z : Slots q) (f : Fin 3)
    (s : Store q) (disk : Disk q) (hp : phase q s=0) (hk : inputCursor q z s=0)
    (hsource : sourceBase q z s+blockCount q.block
      (columns q (s.shapes f)*width q (s.shapes f))≤q.N^q.exponent)
    (htarget : targetBase q z s+count q (s.shapes f)≤q.N^q.exponent)
    (hsep : sourceBase q z s+blockCount q.block
      (columns q (s.shapes f)*width q (s.shapes f))≤targetBase q z s ∨
      targetBase q z s+count q (s.shapes f)≤sourceBase q z s) :
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (scheme q) (3*count q (s.shapes f)) (machine q s disk)=
        (machine q finalStore finalDisk,3*count q (s.shapes f)) ∧
      CommonMarginGather.policy q z f (scheme q) (pack finalStore)=none ∧
      Written q (scheme q) (s.shapes f) (sourceBase q z s) (targetBase q z s)
        (count q (s.shapes f)) disk finalDisk ∧
      (∀ c, c<columns q (s.shapes f) → ∀ j, j<width q (s.shapes f) →
        finalDisk (address q (targetBase q z s) (c*stride q (s.shapes f)+j/q.block))
          ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ =
        disk (address q (sourceBase q z s) ((c*width q (s.shapes f)+j)/q.block))
          ⟨(c*width q (s.shapes f)+j)%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩) ∧
      CommonMovementPolicy.Preserved q s finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  obtain ⟨sf,df,hr,hh,hw,hp',hm⟩ := CommonMarginGather.complete q z f (scheme q)
    s disk hp hk htarget
    (reads_outside q (s.shapes f) (sourceBase q z s) (targetBase q z s) hsource hsep)
  refine ⟨sf,df,hr,hh,hw,?_,hp',hm⟩
  intro c hc j hj
  obtain ⟨hki,huse,hpos⟩ := column_position q.block (width q (s.shapes f))
    (columns q (s.shapes f)) c j (CommonLeafProgram.block_positive q) hc hj
  have hki' : c*stride q (s.shapes f)+j/q.block<count q (s.shapes f) := hki
  have ht : targetBase q z s+(c*stride q (s.shapes f)+j/q.block)<q.N^q.exponent := by omega
  have ha : address q (targetBase q z s) (c*stride q (s.shapes f)+j/q.block)=
      ⟨targetBase q z s+(c*stride q (s.shapes f)+j/q.block),ht⟩ := by
    simp only [address,dif_pos ht]
  rw [ha,hw.written _ hki' ht]
  simp only [stride]
  rw [spec_word q (s.shapes f) (sourceBase q z s) _ disk
    ⟨j%q.block,Nat.mod_lt _ (CommonLeafProgram.block_positive q)⟩ huse]
  simp only [stride,hpos]

/-- Install public dimensions and addresses into the existing RAM fields.
This initializer contains no input values or list of columns. -/
def initialStore (q : Configuration) (z : Slots q) (f : Fin 3)
    (n C : ℕ) (source target : Fin (q.N^q.exponent)) (s : Store q) : Store q :=
  CommonMarginTransform.initialStore q z f n C 0 0 source target s

/-- Complete initialized split of C columns, each containing n words.
The output slab for column c starts at target+c*ceil(n/B). -/
theorem initialized (q : Configuration) (z : Slots q) (f : Fin 3)
    (n C : Fin (q.N^q.exponent+1)) (source target : Fin (q.N^q.exponent))
    (s : Store q) (disk : Disk q)
    (hs : source.val+blockCount q.block (C.val*n.val)≤q.N^q.exponent)
    (ht : target.val+C.val*blockCount q.block n.val≤q.N^q.exponent)
    (hsep : source.val+blockCount q.block (C.val*n.val)≤target.val ∨
      target.val+C.val*blockCount q.block n.val≤source.val) :
    ∃ finalStore finalDisk,
      CommonMarginGather.run q z f (scheme q) (3*(C.val*blockCount q.block n.val))
        (machine q (initialStore q z f n.val C.val source target s) disk)=
        (machine q finalStore finalDisk,3*(C.val*blockCount q.block n.val)) ∧
      CommonMarginGather.policy q z f (scheme q) (pack finalStore)=none ∧
      (∀ c, c<C.val → ∀ j, j<n.val →
        CommonMarginTransform.wordAt q finalDisk (target.val+c*blockCount q.block n.val) j=
        CommonMarginTransform.wordAt q disk source.val (c*n.val+j)) ∧
      (∀ a : Fin (q.N^q.exponent),a.val<target.val ∨
        target.val+C.val*blockCount q.block n.val≤a.val → finalDisk a=disk a) ∧
      CommonMovementPolicy.Preserved q
        (initialStore q z f n.val C.val source target s) finalStore ∧
      Fintype.card (ResidentIndex q)≤q.M := by
  have hn : n.val<(2^q.w)^q.digits := descriptor_capacity q n.val (by have:=n.isLt; omega)
  have hC : C.val<(2^q.w)^q.digits := descriptor_capacity q C.val (by have:=C.isLt; omega)
  have hz : 0<(2^q.w)^q.digits := by positivity
  obtain ⟨hn',hC',_,_⟩ := CommonMarginTransform.shape_fields q n.val C.val 0 0 hn hC hz hz
  let t := initialStore q z f n.val C.val source target s
  have hc := CommonMovementPolicy.initial_control q z ⟨0,by omega⟩ source target
    {s with shapes:=Function.update s.shapes f (CommonMarginTransform.shape q n.val C.val 0 0)}
  have hsb : sourceBase q z t=source.val := hc.source_base
  have htb : targetBase q z t=target.val := hc.target_base
  have hshape : t.shapes f=CommonMarginTransform.shape q n.val C.val 0 0 := by
    simp [t,initialStore,CommonMarginTransform.initialStore,CommonMovementPolicy.initialStore,
      CommonLeafProgram.setPhase]
  have hw : width q (t.shapes f)=n.val := by
    rw [hshape]; exact hn'
  have hcols : columns q (t.shapes f)=C.val := by
    rw [hshape]; exact hC'
  have hstride : stride q (t.shapes f)=blockCount q.block n.val := by rw [stride,hw]
  have hcount : count q (t.shapes f)=C.val*blockCount q.block n.val := by
    rw [count,hcols,hstride]
  obtain ⟨sf,df,hr,hh,hinv,hwords,hpres,hm⟩ := complete q z f t disk hc.phase_zero hc.position
    (by rw [hsb,hcols,hw]; exact hs) (by rw [htb,hcount]; exact ht)
    (by rw [hsb,htb,hcols,hw,hcount]; exact hsep)
  refine ⟨sf,df,?_,hh,?_,?_,hpres,hm⟩
  · simpa only [hcount] using hr
  · intro c hc' j hj
    have hv := hwords c (by rw [hcols]; exact hc') j (by rw [hw]; exact hj)
    rw [htb,hsb,hstride,hw] at hv
    obtain ⟨hki,_,_⟩ := column_position q.block n.val C.val c j
      (CommonLeafProgram.block_positive q) hc' hj
    have hta : target.val+(c*blockCount q.block n.val+j/q.block)<q.N^q.exponent := by omega
    have htotal : c*n.val+j<C.val*n.val := by nlinarith
    have hix : (c*n.val+j)/q.block<blockCount q.block (C.val*n.val) :=
      (cursor_live_iff q.block (C.val*n.val) ((c*n.val+j)/q.block)
        (CommonLeafProgram.block_positive q)).2
        ((Nat.div_mul_le_self (c*n.val+j) q.block).trans_lt htotal)
    have hsa : source.val+(c*n.val+j)/q.block<q.N^q.exponent := by omega
    simpa only [CommonMarginTransform.wordAt,CommonLeafBatchProgram.extendDisk,address,
      Nat.add_assoc,dif_pos hta,dif_pos hsa] using hv
  · simpa only [htb,hcount] using hinv.outside

end CodedSorting.CommonColumnSplit
end Split
