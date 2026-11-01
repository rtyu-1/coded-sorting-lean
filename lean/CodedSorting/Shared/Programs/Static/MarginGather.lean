import CodedSorting.Shared.Memory.MarginTransform
import CodedSorting.Interchange.Framework.Memory.Reflection

/-! A public static compilation of the previously proved two-read margin
scan. Every output block performs two actual reads and one actual write. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonStaticMarginGather
open WordControl CommonSortingNormalization CommonStaticSchedule CommonMarginGather
open CommonLeafProgram (Store Machine Disk machine)
noncomputable section

def secondRead (q : Configuration) (reader : Fin q.inventory.readers)
    (a : Fin (q.N^q.exponent)) (combine : Words q.block q.w → Words q.block q.w → Words q.block q.w) : Instruction q :=
  ⟨.read a (CommonLeafWindow.transferWindow q.inventory q.height q.block q.digits),
    fun ram => let s := unpack ram; pack {s with transfer:=combine (CommonBlockPair.buffer q reader s) s.transfer}⟩

theorem secondRead_step (q : Configuration) (reader : Fin q.inventory.readers)
    (a : Fin (q.N^q.exponent)) (combine : Words q.block q.w → Words q.block q.w → Words q.block q.w)
    (s : Store q) (disk : Disk q) :
    ControlledNormalization.logicalStep (secondRead q reader a combine) (machine q s disk)=
      machine q {s with transfer:=combine (CommonBlockPair.buffer q reader s) (disk a)} disk := by
  simp only [secondRead,ControlledNormalization.logicalStep,Normalization.logicalStep,machine,
    CommonLeafWindow.load_transfer,unpack_pack]
  rfl

theorem secondRead_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (a : Fin (q.N^q.exponent)) (combine : Words q.block q.w → Words q.block q.w → Words q.block q.w) :
    RespectsPC q (secondRead q reader a combine) := by
  apply CommonBlockPair.respectsPC_of_commutes
  intro s
  rw [←CommonBlockPair.machine_eta q s]
  simp only [secondRead_step,CommonBlockPair.erasePC_machine]
  rfl

def fragment (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k : ℕ) : List (Instruction q) :=
  [CommonBlockPair.sourceRead q reader (p.first shape source k),
   secondRead q reader (p.second shape source k) (p.assemble shape k),
   CommonBlockPair.targetWrite q (CommonColumnSplit.address q target k)]

def codeFrom (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target : ℕ) : ℕ → ℕ → List (Instruction q)
  | _,0 => []
  | k,n+1 => fragment q reader p shape source target k ++ codeFrom q reader p shape source target (k+1) n

def code (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target : ℕ) : List (Instruction q) :=
  codeFrom q reader p shape source target 0 (p.count shape)

theorem fragment_raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k : ℕ) (s : Machine q) :
    (executeRaw q (fragment q reader p shape source target k) s).1.disk=
      Function.update s.disk (CommonColumnSplit.address q target k)
        (specBlock q p shape source k s.disk) := by
  rw [←CommonBlockPair.machine_eta q s]
  simp only [fragment,executeRaw,CommonBlockPair.sourceRead_step,secondRead_step,
    CommonBlockPair.targetWrite_step,CommonBlockPair.buffer_stash]
  rfl

theorem fragment_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k : ℕ) :
    ∀ i∈fragment q reader p shape source target k,RespectsPC q i := by
  intro i hi
  simp only [fragment,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact CommonBlockPair.sourceRead_respectsPC q reader _
  · exact secondRead_safe q reader _ _
  · exact CommonBlockPair.targetWrite_respectsPC q _

theorem codeFrom_safe (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k n : ℕ) :
    ∀ i∈codeFrom q reader p shape source target k n,RespectsPC q i := by
  induction n generalizing k with
  | zero => simp [codeFrom]
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · exact fragment_safe q reader p shape source target k i h
    · exact ih (k+1) i h

theorem codeFrom_cost (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k n : ℕ) :
    cost q (codeFrom q reader p shape source target k n)=3*n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.cost_append,ih]
    have h : cost q (fragment q reader p shape source target k)=3 := rfl
    rw [h]; omega

theorem codeFrom_length (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k n : ℕ) :
    (codeFrom q reader p shape source target k n).length=3*n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [codeFrom,List.length_append,ih]; simp [fragment]; omega

theorem raw_from (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target k n : ℕ) (s : Machine q) (original : Disk q)
    (hlen : k+n=p.count shape) (ht : target+p.count shape≤q.N^q.exponent)
    (hsep : ReadsOutside q p shape source target)
    (hinv : Written q p shape source target k original s.disk) :
    Written q p shape source target (p.count shape) original
      (executeRaw q (codeFrom q reader p shape source target k n) s).1.disk := by
  induction n generalizing k s with
  | zero => simpa only [codeFrom,executeRaw,Nat.add_zero] using hlen ▸ hinv
  | succ n ih =>
    rw [codeFrom,CommonPermutationPairs.raw_append]
    apply ih (k+1) _ (by omega)
    have hk : k<p.count shape := by omega
    have htk : target+k<q.N^q.exponent := by omega
    have hr1 := hinv.outside (p.first shape source k) (by
      rcases (hsep k hk).1 with h|h
      · exact Or.inl h
      · exact Or.inr (by omega))
    have hr2 := hinv.outside (p.second shape source k) (by
      rcases (hsep k hk).2 with h|h
      · exact Or.inl h
      · exact Or.inr (by omega))
    rw [fragment_raw]
    have hb : specBlock q p shape source k s.disk=specBlock q p shape source k original := by
      simp only [specBlock,hr1,hr2]
    rw [hb]
    have ha : CommonColumnSplit.address q target k=⟨target+k,htk⟩ := by
      simp [CommonColumnSplit.address,htk]
    rw [ha]
    exact written_succ q p shape source target k original s.disk hinv htk

theorem raw (q : Configuration) (reader : Fin q.inventory.readers)
    (p : Scheme q) (shape : Shape q) (source target : ℕ) (s : Machine q)
    (ht : target+p.count shape≤q.N^q.exponent) (hsep : ReadsOutside q p shape source target) :
    Written q p shape source target (p.count shape) s.disk
      (executeRaw q (code q reader p shape source target) s).1.disk := by
  apply raw_from q reader p shape source target 0 _ s s.disk (by omega) ht hsep
  exact ⟨by intros; omega,by intros; rfl⟩

end
end CodedSorting.CommonStaticMarginGather
