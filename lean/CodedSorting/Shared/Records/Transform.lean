import CodedSorting.Shared.Programs.Static.MarginsRecords
import CodedSorting.Shared.Records.RecordOperations

/-! Composition of actual record programs across changing file sizes.
Every stage uses the same finite disk and protects the same outside region. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CodedSorting.CommonRecordTransform
open CommonSortingNormalization CommonStaticSchedule CommonRecordProgram CommonRecordEncoding
open CommonLeafProgram (Machine)
open CommonPermutationPairs CommonRecordReindex
noncomputable section

structure Stage (q : Configuration) (n m source target origin original buffer limit : ℕ)
    (F : Records q n→Records q m) where
  instructions : List (Instruction q)
  charge : ℕ
  correct : ∀ (s : Machine q) (f : Records q n),Encoded q s.disk source f →
    Encoded q (executeRaw q instructions s).1.disk target (F f)
  frame : ∀ (s : Machine q) (a : Fin (q.N^q.exponent)),
    (a.val<origin ∨ origin+recordBlocks q original≤a.val) →
    (a.val<buffer ∨ limit≤a.val) →(executeRaw q instructions s).1.disk a=s.disk a
  safe : ∀ i∈instructions,RespectsPC q i
  cost_le : cost q instructions≤charge
  length_le : instructions.length≤charge

namespace Stage
variable {q : Configuration} {n m k source middle target origin original buffer limit : ℕ}
variable {F : Records q n→Records q m} {G : Records q m→Records q k}

def append (p : Stage q n m source middle origin original buffer limit F)
    (r : Stage q m k middle target origin original buffer limit G) :
    Stage q n k source target origin original buffer limit (G∘F) where
  instructions := p.instructions++r.instructions
  charge := p.charge+r.charge
  correct := by intro s f hf;rw [raw_append];exact r.correct _ _ (p.correct s f hf)
  frame := by intro s a ho hb;rw [raw_append,r.frame _ a ho hb,p.frame s a ho hb]
  safe := by
    intro i hi
    rcases List.mem_append.mp hi with h|h
    · exact p.safe i h
    · exact r.safe i h
  cost_le := by rw [cost_append];exact Nat.add_le_add p.cost_le r.cost_le
  length_le := by rw [List.length_append];exact Nat.add_le_add p.length_le r.length_le

@[simp] theorem append_charge (p : Stage q n m source middle origin original buffer limit F)
    (r : Stage q m k middle target origin original buffer limit G) :
    (p.append r).charge=p.charge+r.charge := rfl


def castOutput {m' : ℕ} (p : Stage q n m source target origin original buffer limit F)
    (h : m=m') : Stage q n m' source target origin original buffer limit (castRecords h∘F) where
  instructions := p.instructions
  charge := p.charge
  correct := by intro s f hf;exact (encoded_cast q h _ target (F f)).2 (p.correct s f hf)
  frame := p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

@[simp] theorem castOutput_charge {m' : ℕ}
    (p : Stage q n m source target origin original buffer limit F) (h : m=m') :
    (p.castOutput h).charge=p.charge := rfl


def changeFunction {G : Records q n→Records q m}
    (p : Stage q n m source target origin original buffer limit F) (h : F=G) :
    Stage q n m source target origin original buffer limit G := h ▸ p

@[simp] theorem changeFunction_charge {G : Records q n→Records q m}
    (p : Stage q n m source target origin original buffer limit F) (h : F=G) :
    (p.changeFunction h).charge=p.charge := by
  subst G
  rfl


def toProgram {F : Records q n→Records q n}
    (p : Stage q n n source source source n buffer limit F) : Program q n source buffer limit F where
  instructions := p.instructions
  charge := p.charge
  correct := p.correct
  frame := p.frame
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le
@[simp] theorem toProgram_charge {F : Records q n→Records q n}
    (p : Stage q n n source source source n buffer limit F) :
    p.toProgram.charge=p.charge := rfl

end Stage

def workspaceProgram (q : Configuration) {n source work origin original buffer limit : ℕ}
    {F : Records q n→Records q n} (p : Program q n source work limit F)
    (hs : buffer≤source) (he : source+recordBlocks q n≤limit) (hw : buffer≤work) :
    Stage q n n source source origin original buffer limit F where
  instructions := p.instructions
  charge := p.charge
  correct := p.correct
  frame := by
    intro s a _ ha
    apply p.frame s a
    · rcases ha with h|h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rcases ha with h|h
      · exact Or.inl (by omega)
      · exact Or.inr h
  safe := p.safe
  cost_le := p.cost_le
  length_le := p.length_le

@[simp] theorem workspaceProgram_charge (q : Configuration) {n source work origin original buffer limit : ℕ}
    {F : Records q n→Records q n} (p : Program q n source work limit F)
    (hs : buffer≤source) (he : source+recordBlocks q n≤limit) (hw : buffer≤work) :
    (workspaceProgram q (origin:=origin) (original:=original) p hs he hw).charge=p.charge := rfl


def margins (q : Configuration) (reader : Fin q.inventory.readers)
    {K : ℕ} (L N R O source target origin original buffer limit : ℕ) (hKN : O+N≤K)
    (hshape : CommonStaticMargins.ShapeFits q (3*L) (3*N) (3*R) (3*O))
    (hsource : source+recordBlocks q K≤q.N^q.exponent)
    (hs : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤q.N^q.exponent)
    (ht : target+recordBlocks q (L+N+R)≤q.N^q.exponent)
    (hsep : source+max 1 (PhysicalStreamCursor.blockCount q.block (3*O+3*N))≤target ∨
      target+recordBlocks q (L+N+R)≤source)
    (hframe : ∀ a : Fin (q.N^q.exponent),
      (a.val<origin ∨ origin+recordBlocks q original≤a.val) →
      (a.val<buffer ∨ limit≤a.val) → a.val<target ∨ target+recordBlocks q (L+N+R)≤a.val) :
    Stage q K (L+N+R) source target origin original buffer limit
      (CommonStaticMarginsRecords.margin L N R O hKN) where
  instructions := CommonStaticMargins.code q reader (3*L) (3*N) (3*R) (3*O) source target
  charge := 3*recordBlocks q (L+N+R)
  correct := by
    intro s f hf
    apply CommonStaticMarginsRecords.raw_encoded q reader L N R O source target hKN f s hf hshape hsource hs
    · simpa only [recordBlocks_eq_words,Nat.mul_add] using ht
    · simpa only [recordBlocks_eq_words,Nat.mul_add] using hsep
  frame := by
    intro s a ho hb
    have hr := (CommonStaticMargins.raw q reader (3*L) (3*N) (3*R) (3*O) source target s hshape hs
      (by simpa only [recordBlocks_eq_words,Nat.mul_add] using ht)
      (by simpa only [recordBlocks_eq_words,Nat.mul_add] using hsep)).2
    apply hr a
    simpa only [recordBlocks_eq_words,Nat.mul_add] using hframe a ho hb
  safe := CommonStaticMargins.safe q reader (3*L) (3*N) (3*R) (3*O) source target
  cost_le := by
    rw [CommonStaticMargins.cost_eq q reader (3*L) (3*N) (3*R) (3*O) source target hshape,
      recordBlocks_eq_words,Nat.mul_add,Nat.mul_add]
  length_le := by
    rw [CommonStaticMargins.length_eq q reader (3*L) (3*N) (3*R) (3*O) source target hshape,
      recordBlocks_eq_words,Nat.mul_add,Nat.mul_add]

end
end CodedSorting.CommonRecordTransform
