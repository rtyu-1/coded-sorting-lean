# Directory 的定义

[源码](Directory.lean) · [主定理导读](../../Theorem31/Definitions.zh-CN.md) · [基础概念](../../../../docs/FoundationDefinitions.zh-CN.md)

本页根据 Lean 编译后的声明生成。每个项目依赖都有继续阅读的链接；证明项由 Lean 检查。`⋯` 表示打印时省略的证明或较长子表达式，原始定义可从源码位置完整查看。

<a id="def-760fcffc97ab4f49"></a>
## `CodedSorting.CommonMSDDirectory.start`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L19)

**类型**

```lean
{K : ℕ} → (Fin K → ℕ) → Fin K → ℕ
```

**定义**

```lean
fun {K} values k => ∑ j, if j < k then values j else 0
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Finset.univ`, `instOfNatNat`, `Fin.fintype`, `Fin.decLt`, `Nat`, `LT.lt`, `instLTFin`, `Nat.instAddCommMonoid`, `OfNat.ofNat`, `Fin`, `Finset.sum`, `ite`

<a id="def-249c403307c474d4"></a>
## `CodedSorting.CommonMSDDirectory.value`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L22)

**类型**

```lean
{K : ℕ} → (Fin K → ℕ) → Fin (K * 2) → ℕ
```

**定义**

```lean
fun {K} values i =>
  let p := finProdFinEquiv.symm i;
  if ↑p.2 = 0 then CodedSorting.CommonMSDDirectory.start values p.1 else values p.1
```

**继续展开**

- [CodedSorting.CommonMSDDirectory.start](Directory.definitions.md#def-760fcffc97ab4f49)

**基础库名称**

`Equiv.instFunLike`, `HMul.hMul`, `Equiv`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Prod.fst`, `Nat`, `finProdFinEquiv`, `instDecidableEqNat`, `Equiv.symm`, `Prod`, `OfNat.ofNat`, `Fin`, `Eq`, `Prod.snd`, `DFunLike.coe`, `instHMul`, `ite`

<a id="def-ab180bac12c47043"></a>
## `CodedSorting.CommonMSDDirectory.smallFit`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L37)

**类型**

```lean
∀ {K : ℕ} (q : CodedSorting.CommonSortingNormalization.Configuration),
  K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
    K * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q
```

**定义**

```lean
fun {K} q hfit =>
  le_of_not_gt fun a =>
    Linarith.lt_irrefl
      (Eq.mp
        (congrArg (fun _a => _a < 0)
          (Mathlib.Tactic.Ring.of_eq
            (Mathlib.Tactic.Ring.add_congr
              (Mathlib.Tactic.Ring.add_congr
                (Mathlib.Tactic.Ring.add_congr
                  (Mathlib.Tactic.Ring.mul_congr
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 2)))
                    (Mathlib.Tactic.Ring.neg_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 1)))
                      (Mathlib.Tactic.Ring.neg_add
                        (Mathlib.Tactic.Ring.neg_one_mul
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.neg_zero))
                    (Mathlib.Tactic.Ring.add_mul
                      (Mathlib.Tactic.Ring.mul_add
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 2))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1)) (Eq.refl (Int.negOfNat 2))))
                        (Mathlib.Tactic.Ring.mul_zero (Nat.rawCast 2))
                        (Mathlib.Tactic.Ring.add_pf_add_zero ((Int.negOfNat 2).rawCast + 0)))
                      (Mathlib.Tactic.Ring.zero_mul ((Int.negOfNat 1).rawCast + 0))
                      (Mathlib.Tactic.Ring.add_pf_add_zero ((Int.negOfNat 2).rawCast + 0))))
                  (Mathlib.Tactic.Ring.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 0)))
                    (Mathlib.Tactic.Ring.atom_pf ↑(CodedSorting.CommonExchangeLeaf.bankWords q))
                    (Mathlib.Tactic.Ring.sub_pf
                      (Mathlib.Tactic.Ring.neg_add
                        (Mathlib.Tactic.Ring.neg_mul (↑(CodedSorting.CommonExchangeLeaf.bankWords q)) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.neg_one_mul
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        Mathlib.Tactic.Ring.neg_zero)
                      (Mathlib.Tactic.Ring.add_pf_zero_add
                        (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                          0))))
                  (Mathlib.Tactic.Ring.add_pf_add_lt (Int.negOfNat 2).rawCast
                    (Mathlib.Tactic.Ring.add_pf_zero_add
                      (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                (Mathlib.Tactic.Ring.sub_congr
                  (Mathlib.Tactic.Ring.mul_congr
                    (Mathlib.Tactic.Ring.mul_congr (Mathlib.Tactic.Ring.atom_pf ↑K)
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 2)))
                      (Mathlib.Tactic.Ring.add_mul
                        (Mathlib.Tactic.Ring.mul_add
                          (Mathlib.Tactic.Ring.mul_pf_left (↑K) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.one_mul (Nat.rawCast 2)))
                          (Mathlib.Tactic.Ring.mul_zero (↑K ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.add_pf_add_zero (↑K ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                        (Mathlib.Tactic.Ring.zero_mul (Nat.rawCast 2 + 0))
                        (Mathlib.Tactic.Ring.add_pf_add_zero (↑K ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                    (Mathlib.Tactic.Ring.atom_pf ↑q.digits)
                    (Mathlib.Tactic.Ring.add_mul
                      (Mathlib.Tactic.Ring.mul_add
                        (Mathlib.Tactic.Ring.mul_pf_left (↑K) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.mul_pf_right (↑q.digits) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.mul_one (Nat.rawCast 2))))
                        (Mathlib.Tactic.Ring.mul_zero (↑K ^ Nat.rawCast 1 * Nat.rawCast 2))
                        (Mathlib.Tactic.Ring.add_pf_add_zero
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                      (Mathlib.Tactic.Ring.zero_mul (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.add_pf_add_zero
                        (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                  (Mathlib.Tactic.Ring.atom_pf ↑(CodedSorting.CommonExchangeLeaf.bankWords q))
                  (Mathlib.Tactic.Ring.sub_pf
                    (Mathlib.Tactic.Ring.neg_add
                      (Mathlib.Tactic.Ring.neg_mul (↑(CodedSorting.CommonExchangeLeaf.bankWords q)) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.neg_one_mul
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 1))
                              (Eq.refl (Int.negOfNat 1))))))
                      Mathlib.Tactic.Ring.neg_zero)
                    (Mathlib.Tactic.Ring.add_pf_add_gt
                      (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.add_pf_add_zero
                        (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))))
                (Mathlib.Tactic.Ring.add_pf_add_lt (Int.negOfNat 2).rawCast
                  (Mathlib.Tactic.Ring.add_pf_add_overlap
                    (Mathlib.Tactic.Ring.add_overlap_pf (↑(CodedSorting.CommonExchangeLeaf.bankWords q)) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1)) (Eq.refl (Int.negOfNat 2)))))
                    (Mathlib.Tactic.Ring.add_pf_zero_add
                      (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))))
              (Mathlib.Tactic.Ring.mul_congr
                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 2)))
                (Mathlib.Tactic.Ring.sub_congr
                  (Mathlib.Tactic.Ring.add_congr
                    (Mathlib.Tactic.Ring.atom_pf ↑(CodedSorting.CommonExchangeLeaf.bankWords q))
                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 1)))
                    (Mathlib.Tactic.Ring.add_pf_add_gt (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.add_pf_add_zero
                        (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                  (Mathlib.Tactic.Ring.mul_congr (Mathlib.Tactic.Ring.atom_pf ↑K)
                    (Mathlib.Tactic.Ring.atom_pf ↑q.digits)
                    (Mathlib.Tactic.Ring.add_mul
                      (Mathlib.Tactic.Ring.mul_add
                        (Mathlib.Tactic.Ring.mul_pf_left (↑K) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.mul_pf_right (↑q.digits) (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.one_mul (Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.mul_zero (↑K ^ Nat.rawCast 1 * Nat.rawCast 1))
                        (Mathlib.Tactic.Ring.add_pf_add_zero
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                      (Mathlib.Tactic.Ring.zero_mul (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.add_pf_add_zero
                        (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                  (Mathlib.Tactic.Ring.sub_pf
                    (Mathlib.Tactic.Ring.neg_add
                      (Mathlib.Tactic.Ring.neg_mul (↑K) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.neg_mul (↑q.digits) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.neg_one_mul
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 1))
                                (Eq.refl (Int.negOfNat 1)))))))
                      Mathlib.Tactic.Ring.neg_zero)
                    (Mathlib.Tactic.Ring.add_pf_add_lt (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.add_pf_add_lt
                        (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.add_pf_zero_add
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) + 0))))))
                (Mathlib.Tactic.Ring.add_mul
                  (Mathlib.Tactic.Ring.mul_add (Mathlib.Tactic.Ring.mul_one (Nat.rawCast 2))
                    (Mathlib.Tactic.Ring.mul_add
                      (Mathlib.Tactic.Ring.mul_pf_right (↑(CodedSorting.CommonExchangeLeaf.bankWords q)) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.mul_one (Nat.rawCast 2)))
                      (Mathlib.Tactic.Ring.mul_add
                        (Mathlib.Tactic.Ring.mul_pf_right (↑K) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.mul_pf_right (↑q.digits) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 2))
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 1)) (Eq.refl (Int.negOfNat 2))))))
                        (Mathlib.Tactic.Ring.mul_zero (Nat.rawCast 2))
                        (Mathlib.Tactic.Ring.add_pf_add_zero
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 2).rawCast) + 0)))
                      (Mathlib.Tactic.Ring.add_pf_add_lt
                        (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 2)
                        (Mathlib.Tactic.Ring.add_pf_zero_add
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 2).rawCast) + 0))))
                    (Mathlib.Tactic.Ring.add_pf_add_lt (Nat.rawCast 2)
                      (Mathlib.Tactic.Ring.add_pf_zero_add
                        (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 2 +
                          (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 2).rawCast) + 0)))))
                  (Mathlib.Tactic.Ring.zero_mul
                    (Nat.rawCast 1 +
                      (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 1 +
                        (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) + 0))))
                  (Mathlib.Tactic.Ring.add_pf_add_zero
                    (Nat.rawCast 2 +
                      (↑(CodedSorting.CommonExchangeLeaf.bankWords q) ^ Nat.rawCast 1 * Nat.rawCast 2 +
                        (↑K ^ Nat.rawCast 1 * (↑q.digits ^ Nat.rawCast 1 * (Int.negOfNat 2).rawCast) + 0))))))
              (Mathlib.Tactic.Ring.add_pf_add_overlap_zero
                (Mathlib.Meta.NormNum.IsInt.to_isNat
                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                    (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 2))
                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 2))
                    (Eq.refl (Int.ofNat 0))))
                (Mathlib.Tactic.Ring.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.add_overlap_pf_zero (↑(CodedSorting.CommonExchangeLeaf.bankWords q))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 2))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 2))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.add_overlap_pf_zero (↑K) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.add_overlap_pf_zero (↑q.digits) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℤ 2))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℤ (Int.negOfNat 2)) (Eq.refl (Int.ofNat 0))))))
                    (Mathlib.Tactic.Ring.add_pf_zero_add 0)))))
            (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 0)))))
        (Linarith.add_lt_of_neg_of_le
          (Linarith.add_lt_of_neg_of_le
            (Linarith.add_lt_of_neg_of_le
              (Linarith.mul_neg (neg_neg_of_pos Linarith.zero_lt_one)
                (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 0))
                  (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 2)) (Eq.refl false)))
              (Linarith.sub_nonpos_of_le (Linarith.natCast_nonneg ℤ (CodedSorting.CommonExchangeLeaf.bankWords q))))
            (Linarith.sub_nonpos_of_le
              (id
                (Eq.mp
                  (Eq.trans (_proof_2✝ (K * 2 * q.digits) (CodedSorting.CommonExchangeLeaf.bankWords q))
                    (congrArg (fun x => x ≤ ↑(CodedSorting.CommonExchangeLeaf.bankWords q))
                      (Eq.trans (Nat.cast_mul (K * 2) q.digits)
                        (congrArg (fun x => x * ↑q.digits) (Nat.cast_mul K 2)))))
                  hfit))))
          (Linarith.mul_nonpos
            (Linarith.sub_nonpos_of_le
              (Int.add_one_le_iff.mpr
                (id
                  (Eq.mp
                    (Eq.trans (_proof_3✝ (CodedSorting.CommonExchangeLeaf.bankWords q) (K * q.digits))
                      (congrArg (LT.lt ↑(CodedSorting.CommonExchangeLeaf.bankWords q)) (Nat.cast_mul K q.digits)))
                    a))))
            (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 0))
              (Mathlib.Meta.NormNum.isNat_ofNat ℤ (Eq.refl 2)) (Eq.refl false)))))
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`Int.instAddCommGroup`, `Iff.mpr`, `NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring`, `NegZeroClass.toNeg`, `NonAssocSemiring.toAddCommMonoidWithOne`, `Int.instIsStrictOrderedRing`, `Preorder.toLT`, `NonUnitalCommRing.toNonUnitalNonAssocCommRing`, `HMul.hMul`, `Nat.rawCast`, `AddMonoid.toAddSemigroup`, `Ring.toNonAssocRing`, `Mathlib.Tactic.Ring.mul_zero`, `Mathlib.Tactic.Ring.mul_pf_left`, `AddGroupWithOne.toAddGroup`, `Mathlib.Tactic.Ring.add_pf_add_gt`, `congrArg`, `CommSemiring.toSemiring`, `Mathlib.Tactic.Ring.add_overlap_pf_zero`, `Mathlib.Tactic.Ring.neg_congr`, `Mathlib.Tactic.Ring.neg_zero`, `Mathlib.Tactic.Ring.mul_pf_right`, `Int.rawCast`, `PartialOrder.toPreorder`, `Mathlib.Tactic.Ring.one_mul`, `AddGroupWithOne.toAddMonoidWithOne`, `HSub.hSub`, `Mathlib.Tactic.Ring.zero_mul`, `Mathlib.Meta.NormNum.IsNat.of_raw`, `NonUnitalNonAssocSemiring.toMulZeroClass`, `_private.Mathlib.Tactic.Zify.0._proof_2`, `Mathlib.Tactic.Ring.instCommSemiringNat`, `Int.add_one_le_iff`, `Linarith.natCast_nonneg`, `le_of_not_gt`, `SemilatticeInf.toPartialOrder`, `Monoid.toNatPow`, `Mathlib.Tactic.Ring.cast_zero`, `Mathlib.Tactic.Ring.neg_mul`, `Eq.mp`, `Mathlib.Tactic.Ring.sub_pf`, `Mathlib.Tactic.Ring.neg_add`, `id`, `Distrib.toAdd`, `Mathlib.Tactic.Ring.add_pf_add_overlap`, `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`, `AddMonoidWithOne.toNatCast`, `Int.ofNat`, `instMulNat`, `SubtractionMonoid.toSubNegZeroMonoid`, `instOfNatNat`, `Int`, `AddCommMonoidWithOne.toAddMonoidWithOne`, `Int.instAddMonoid`, `Mathlib.Tactic.Ring.sub_congr`, `Mathlib.Meta.NormNum.isNat_ofNat`, `Mathlib.Meta.NormNum.isInt_mul`, `LE.le`, `instLENat`, `SubNegZeroMonoid.toNegZeroClass`, `Mathlib.Tactic.Ring.of_eq`, `NormedCommRing.toNonUnitalNormedCommRing`, `Mathlib.Tactic.Ring.add_pf_zero_add`, `SubtractionCommMonoid.toSubtractionMonoid`, `Nat.cast`, `NonAssocRing.toNonUnitalNonAssocRing`, `Mathlib.Tactic.Ring.mul_congr`, `SubNegMonoid.toSub`, `Int.instLTInt`, `AddMonoidWithOne.toOne`, `Int.instNormedCommRing`, `Mathlib.Tactic.Ring.add_mul`, `GT.gt`, `instHAdd`, `AddSemigroup.toAdd`, `Mathlib.Tactic.Ring.add_pf_add_zero`, `instHSub`, `instNatAtLeastTwo`, `Mathlib.Tactic.Ring.add_pf_add_overlap_zero`, `Nat.cast_mul`, `AddGroup.toSubNegMonoid`, `Mathlib.Meta.NormNum.IsInt.to_raw_eq`, `HPow.hPow`, `instOfNat`, `Distrib.toMul`, `HAdd.hAdd`, `IsStrictOrderedRing.toIsOrderedRing`, `Mathlib.Meta.NormNum.IsInt.to_isNat`, `NonAssocSemiring.toNonUnitalNonAssocSemiring`, `Linarith.mul_nonpos`, `Mathlib.Tactic.Ring.add_overlap_pf`, `Int.instRing`, `Nat`, `Mathlib.Tactic.Ring.mul_one`, `LT.lt`, `Linarith.add_lt_of_neg_of_le`, `instLatticeInt`, `Mathlib.Tactic.Ring.add_pf_add_lt`, `Bool`, `Int.instAdd`, `One.toOfNat1`, `NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring`, `NonUnitalNonAssocSemiring.toDistrib`, `Zero.toOfNat0`, `Mathlib.Meta.NormNum.isInt_add`, `Eq.refl`, `neg_neg_of_pos`, `Mathlib.Meta.NormNum.IsInt.of_raw`, `_private.Mathlib.Tactic.Zify.0._proof_3`, `Mathlib.Meta.NormNum.isNat_lt_true`, `instNatCastInt`, `instHPow`, `Mathlib.Tactic.Ring.cast_pos`, `NonUnitalNormedCommRing.toNonUnitalCommRing`, `instLTNat`, `Mathlib.Tactic.Ring.atom_pf`, `AddCommGroup.toDivisionAddCommMonoid`, `Linarith.sub_nonpos_of_le`, `Int.instCommSemiring`, `Int.instCharZero`, `OfNat.ofNat`, `Bool.false`, `LinearOrder.toPartialOrder`, `Linarith.lt_irrefl`, `Semiring.toNonAssocSemiring`, `Ring.toSemiring`, `Linarith.zero_lt_one`, `Mathlib.Tactic.Ring.neg_one_mul`, `Ring.toAddGroupWithOne`, `instOfNatAtLeastTwo`, `Neg.neg`, `MonoidWithZero.toMonoid`, `Mathlib.Tactic.Ring.mul_add`, `Int.instLEInt`, `Eq.trans`, `Int.negOfNat`, `MulZeroClass.toZero`, `Lattice.toSemilatticeInf`, `Mathlib.Tactic.Ring.add_congr`, `Int.instSemiring`, `Mathlib.Meta.NormNum.IsNat.to_isInt`, `Semiring.toMonoidWithZero`, `instHMul`, `Linarith.mul_neg`, `Int.instIsOrderedAddMonoid`, `Nat.instLinearOrder`

<a id="def-adf99eaa77bbdd37"></a>
## `CodedSorting.CommonMSDDirectory.formatStore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L41)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun {K} q hfit s =>
  CodedSorting.CommonMSDDirectoryScan.putCounters q
    (CodedSorting.CommonMSDDirectory.value fun k => CodedSorting.CommonMSDDirectoryScan.counter q ⋯ s k) s
```

**继续展开**

- [CodedSorting.CommonMSDDirectory.smallFit](Directory.definitions.md#def-ab180bac12c47043)
- [CodedSorting.CommonMSDDirectoryScan.counter](CountSemantics.definitions.md#def-fdbe0c02f096da72)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonMSDDirectoryScan.putCounters](CountSemantics.definitions.md#def-5029535870be07ae)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDDirectory.value](Directory.definitions.md#def-249c403307c474d4)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-ea4fd82f8dcc0e7f"></a>
## `CodedSorting.CommonMSDDirectory.formatInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L45)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun {K} q hfit =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDDirectory.formatStore q hfit (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonMSDDirectory.formatStore](Directory.definitions.md#def-adf99eaa77bbdd37)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`HMul.hMul`, `Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`, `instHMul`

<a id="def-2a36fe66dfedd827"></a>
## `CodedSorting.CommonMSDDirectory.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L49)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q K => CodedSorting.PhysicalStreamCursor.blockCount q.block (K * 2 * q.digits)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-120095f3e5df81f1"></a>
## `CodedSorting.CommonMSDDirectory.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L52)

**类型**

```lean
{K : ℕ} →
  (q : CodedSorting.CommonSortingNormalization.Configuration) →
    K * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q →
      (CodedSorting.WordControl.Word q.w → Fin K) → ℕ → ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun {K} q hfit key source n target =>
  CodedSorting.CommonMSDDirectoryScan.code q ⋯ key source n ++
      [CodedSorting.CommonMSDDirectory.formatInstruction q hfit] ++
    CodedSorting.CommonStaticLeaf.writeCode q target (K * 2 * q.digits) (CodedSorting.CommonMSDDirectory.blocks q K)
```

**继续展开**

- [CodedSorting.CommonMSDDirectory.smallFit](Directory.definitions.md#def-ab180bac12c47043)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonMSDDirectoryScan.code](CountSemantics.definitions.md#def-95755ebe28609e42)
- [CodedSorting.CommonMSDDirectory.formatInstruction](Directory.definitions.md#def-ea4fd82f8dcc0e7f)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonStaticLeaf.writeCode](../../../Shared/Programs/Static/Leaf.definitions.md#def-d8b6afa318659a57)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDDirectory.blocks](Directory.definitions.md#def-2a36fe66dfedd827)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `List.cons`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `OfNat.ofNat`, `Fin`, `HAppend.hAppend`, `instHMul`, `List.nil`

<a id="def-4a6811d8643da8a2"></a>
## `CodedSorting.CommonMSDDirectoryRead.offset`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L249)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q e => e * (2 * q.digits)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-285c894a4f841721"></a>
## `CodedSorting.CommonMSDDirectoryRead.lead`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L250)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q e => CodedSorting.CommonMSDDirectoryRead.offset q e % q.block
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.offset](Directory.definitions.md#def-4a6811d8643da8a2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat.instMod`, `instHMod`, `HMod.hMod`, `Nat`

<a id="def-5085ee06799b0532"></a>
## `CodedSorting.CommonMSDDirectoryRead.total`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L251)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q e => CodedSorting.CommonMSDDirectoryRead.lead q e + 2 * q.digits
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.lead](Directory.definitions.md#def-285c894a4f841721)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `instHMul`

<a id="def-752528505bfa3622"></a>
## `CodedSorting.CommonMSDDirectoryRead.base`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L252)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ → ℕ
```

**定义**

```lean
fun q target e => target + CodedSorting.CommonMSDDirectoryRead.offset q e / q.block
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.offset](Directory.definitions.md#def-4a6811d8643da8a2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`instHDiv`, `HDiv.hDiv`, `instHAdd`, `HAdd.hAdd`, `Nat`, `Nat.instDiv`, `instAddNat`

<a id="def-3e4edd55c6d441b1"></a>
## `CodedSorting.CommonMSDDirectoryRead.blocks`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L253)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ → ℕ
```

**定义**

```lean
fun q e => CodedSorting.PhysicalStreamCursor.blockCount q.block (CodedSorting.CommonMSDDirectoryRead.total q e)
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.total](Directory.definitions.md#def-5085ee06799b0532)
- [CodedSorting.PhysicalStreamCursor.blockCount](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-e3e2890b8a9b4db3)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)

**基础库名称**

`Nat`

<a id="def-7b106aceec8b4ea3"></a>
## `CodedSorting.CommonMSDDirectoryRead.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L255)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q target e =>
  CodedSorting.CommonStaticLeaf.readCode q (CodedSorting.CommonMSDDirectoryRead.base q target e)
    (CodedSorting.CommonMSDDirectoryRead.total q e) (CodedSorting.CommonMSDDirectoryRead.blocks q e)
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.total](Directory.definitions.md#def-5085ee06799b0532)
- [CodedSorting.CommonMSDDirectoryRead.base](Directory.definitions.md#def-752528505bfa3622)
- [CodedSorting.CommonMSDDirectoryRead.blocks](Directory.definitions.md#def-3e4edd55c6d441b1)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonStaticLeaf.readCode](../../../Shared/Programs/Static/Leaf.definitions.md#def-292caf1044d209bc)

**基础库名称**

`List`, `Nat`

<a id="def-24b8cb75564b2e83"></a>
## `CodedSorting.CommonMSDDirectoryRead.fieldWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L258)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → Fin 2 → CodedSorting.CommonLeafProgram.Store q → CodedSorting.WordControl.Words q.digits q.w
```

**定义**

```lean
fun q e field s j =>
  CodedSorting.ResidentLeafBank.getWord s.leaf (CodedSorting.CommonMSDDirectoryRead.lead q e + ↑field * q.digits + ↑j)
```

**继续展开**

- [CodedSorting.CommonMSDDirectoryRead.lead](Directory.definitions.md#def-285c894a4f841721)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.ResidentLeafBank.getWord](../../../Shared/Memory/ResidentLeafBank.definitions.md#def-43482f33d26d74a0)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-7259c12452aec226"></a>
## `CodedSorting.CommonMSDDirectoryRead.field`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L261)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → Fin 2 → CodedSorting.CommonLeafProgram.Store q → ℕ
```

**定义**

```lean
fun q e which s => CodedSorting.WordControl.decodeWords (CodedSorting.CommonMSDDirectoryRead.fieldWords q e which s)
```

**继续展开**

- [CodedSorting.WordControl.decodeWords](../../../Shared/Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDDirectoryRead.fieldWords](Directory.definitions.md#def-24b8cb75564b2e83)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`instOfNatNat`, `Nat`, `OfNat.ofNat`, `Fin`

<a id="def-37ce7cf4d9d29a25"></a>
## `CodedSorting.CommonMSDChildCount.accWords`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L496)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  CodedSorting.CommonLeafProgram.Store q → CodedSorting.WordControl.Words q.digits q.w
```

**定义**

```lean
fun q s j => s.shapes 0 ⟨↑j, ⋯⟩
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.accWords._proof_3](Directory.definitions.md#def-91227404ea71bdb1)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.CommonMSDChildCount.accWords._proof_2](Directory.definitions.md#def-6debdfe64b89039a)

**基础库名称**

`HMul.hMul`, `Fin.mk`, `Fin.instOfNat`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-6019ebd193440039"></a>
## `CodedSorting.CommonMSDChildCount.acc`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L499)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonLeafProgram.Store q → ℕ
```

**定义**

```lean
fun q s => CodedSorting.WordControl.decodeWords (CodedSorting.CommonMSDChildCount.accWords q s)
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.accWords](Directory.definitions.md#def-37ce7cf4d9d29a25)
- [CodedSorting.WordControl.decodeWords](../../../Shared/Words/WordConvention.definitions.md#def-11c782157f026c8c)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)

**基础库名称**

`Nat`

<a id="def-e40fcd58b6aaec3b"></a>
## `CodedSorting.CommonMSDChildCount.setAcc`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L501)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q value s =>
  { leaf := s.leaf, readers := s.readers, writers := s.writers, transfer := s.transfer, scalars := s.scalars,
    directories := s.directories,
    shapes :=
      Function.update s.shapes 0 fun i =>
        if h : ↑i < q.digits then CodedSorting.PhysicalStreamCursor.encodeNat q.digits q.w value ⟨↑i, h⟩
        else s.shapes 0 i,
    top := s.top, pcs := s.pcs }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.SourceState.transfer](../../Resources/Framework/NormalizationFrames.definitions.md#def-5af33a923e775e41)
- [CodedSorting.CommonSortingNormalization.SourceState.pcs](../../Resources/Framework/NormalizationFrames.definitions.md#def-5b02f957dea973c7)
- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.SourceState.directories](../../Resources/Framework/NormalizationFrames.definitions.md#def-443c651ce7b31bd4)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.PhysicalStreamCursor.encodeNat](../../../Shared/Memory/PhysicalStreamCursor.definitions.md#def-0b39ac6782c7ab72)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.SourceState.top](../../Resources/Framework/NormalizationFrames.definitions.md#def-61729c1e88340c1b)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonSortingNormalization.SourceState.leaf](../../Resources/Framework/NormalizationFrames.definitions.md#def-c74201da4a42b2fb)
- [CodedSorting.CommonSortingNormalization.SourceState.shapes](../../Resources/Framework/NormalizationFrames.definitions.md#def-8b7d876f6d0e844e)
- [CodedSorting.CommonSortingNormalization.SourceState.mk](../../Resources/Framework/NormalizationFrames.definitions.md#def-72de523b32bd3bcb)
- [CodedSorting.CommonSortingNormalization.SourceState.writers](../../Resources/Framework/NormalizationFrames.definitions.md#def-c3d33757cbee4c66)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonSortingNormalization.SourceState.readers](../../Resources/Framework/NormalizationFrames.definitions.md#def-1ce3f0d449f8cfec)
- [CodedSorting.WordControl.Words](../../../Shared/Words/WordConvention.definitions.md#def-6ff0251bdd746fcb)
- [CodedSorting.CommonMSDChildCount.accWords._proof_2](Directory.definitions.md#def-6debdfe64b89039a)
- [CodedSorting.CommonSortingNormalization.SourceState.scalars](../../Resources/Framework/NormalizationFrames.definitions.md#def-e8ae6388c01bfd91)

**基础库名称**

`Function.update`, `HMul.hMul`, `instDecidableEqFin`, `Fin.mk`, `Fin.instOfNat`, `instMulNat`, `instOfNatNat`, `Fin.val`, `dite`, `Nat`, `LT.lt`, `Nat.decLt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `Not`, `instHMul`

<a id="def-109392984c3a324e"></a>
## `CodedSorting.CommonMSDChildCount.initInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L517)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDChildCount.setAcc q 0 (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonMSDChildCount.setAcc](Directory.definitions.md#def-e40fcd58b6aaec3b)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `instOfNatNat`, `HPow.hPow`, `Nat`, `instHPow`, `OfNat.ofNat`

<a id="def-f49fed24cb26abeb"></a>
## `CodedSorting.CommonMSDChildCount.addStore`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L520)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → CodedSorting.CommonLeafProgram.Store q → CodedSorting.CommonLeafProgram.Store q
```

**定义**

```lean
fun q key s =>
  CodedSorting.CommonMSDChildCount.setAcc q
    (CodedSorting.CommonMSDChildCount.acc q s + CodedSorting.CommonMSDDirectoryRead.field q key 1 s) s
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.addStore._proof_4](Directory.definitions.md#def-29d4937227bc9062)
- [CodedSorting.CommonMSDChildCount.setAcc](Directory.definitions.md#def-e40fcd58b6aaec3b)
- [CodedSorting.CommonMSDChildCount.acc](Directory.definitions.md#def-6019ebd193440039)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonLeafProgram.Store](../../../Shared/Memory/Leaf/Program.definitions.md#def-e3c14c4bd7f3ac1c)
- [CodedSorting.CommonMSDDirectoryRead.field](Directory.definitions.md#def-7259c12452aec226)

**基础库名称**

`Fin.instOfNat`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `OfNat.ofNat`, `Fin`

<a id="def-701c97e584ebeb6a"></a>
## `CodedSorting.CommonMSDChildCount.addInstruction`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L523)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) → ℕ → CodedSorting.CommonStaticSchedule.Instruction q
```

**定义**

```lean
fun q key =>
  {
    operation :=
      CodedSorting.Normalization.Command.localOp fun ram =>
        CodedSorting.CommonSortingNormalization.pack
          (CodedSorting.CommonMSDChildCount.addStore q key (CodedSorting.CommonSortingNormalization.unpack ram)),
    resume := id }
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.inventory](../../Resources/Framework/NormalizationFrames.definitions.md#def-b7bca164f5a6f55d)
- [CodedSorting.WordControl.Word](../../../Shared/Words/WordConvention.definitions.md#def-5ac34e3d8146967b)
- [CodedSorting.CommonSortingNormalization.Configuration.ramWords](../../Resources/Framework/NormalizationFrames.definitions.md#def-7d7f7ce8536ebbdd)
- [CodedSorting.CommonSortingNormalization.Configuration.w](../../Resources/Framework/NormalizationFrames.definitions.md#def-d94a6ee84fc22f76)
- [CodedSorting.CommonSortingNormalization.Configuration.exponent](../../Resources/Framework/NormalizationFrames.definitions.md#def-441ef1e5176fbf68)
- [CodedSorting.CommonSortingNormalization.pack](../../Resources/Framework/NormalizationFrames.definitions.md#def-1890a68cf8f15384)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.ControlledNormalization.Instruction.mk](../../../Shared/Programs/ControlledNormalization.definitions.md#def-5b44b5b9869102be)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.Normalization.Words](../../../Shared/Programs/Normalization.definitions.md#def-674596978a99f625)
- [CodedSorting.CommonMSDChildCount.addStore](Directory.definitions.md#def-f49fed24cb26abeb)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.Normalization.Command.localOp](../../../Shared/Programs/Normalization.definitions.md#def-9456a9cd06b765ae)
- [CodedSorting.CommonSortingNormalization.Configuration.N](../../Resources/Framework/NormalizationFrames.definitions.md#def-a0f8cfde18f80cba)
- [CodedSorting.CommonSortingNormalization.Configuration.block](../../Resources/Framework/NormalizationFrames.definitions.md#def-32bdace0e0767974)
- [CodedSorting.CommonSortingNormalization.unpack](../../Resources/Framework/NormalizationFrames.definitions.md#def-8a0c8f74cc8bea51)

**基础库名称**

`Nat.instMonoid`, `Monoid.toNatPow`, `id`, `HPow.hPow`, `Nat`, `instHPow`

<a id="def-57208af997a48790"></a>
## `CodedSorting.CommonMSDChildCount.fragment`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L526)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q directory key =>
  CodedSorting.CommonMSDDirectoryRead.code q directory key ++ [CodedSorting.CommonMSDChildCount.addInstruction q key]
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.addInstruction](Directory.definitions.md#def-701c97e584ebeb6a)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)
- [CodedSorting.CommonMSDDirectoryRead.code](Directory.definitions.md#def-7b106aceec8b4ea3)

**基础库名称**

`List.cons`, `instHAppendOfAppend`, `List`, `Nat`, `List.instAppend`, `HAppend.hAppend`, `List.nil`

<a id="def-17306a30d7c126ad"></a>
## `CodedSorting.CommonMSDChildCount.body`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L529)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q directories key => List.flatMap (fun target => CodedSorting.CommonMSDChildCount.fragment q target key) directories
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.fragment](Directory.definitions.md#def-57208af997a48790)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List`, `Nat`, `List.flatMap`

<a id="def-9c5b1d8ac2d0db62"></a>
## `CodedSorting.CommonMSDChildCount.code`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L532)

**类型**

```lean
(q : CodedSorting.CommonSortingNormalization.Configuration) →
  List ℕ → ℕ → List (CodedSorting.CommonStaticSchedule.Instruction q)
```

**定义**

```lean
fun q directories key =>
  CodedSorting.CommonMSDChildCount.initInstruction q :: CodedSorting.CommonMSDChildCount.body q directories key
```

**继续展开**

- [CodedSorting.CommonMSDChildCount.initInstruction](Directory.definitions.md#def-109392984c3a324e)
- [CodedSorting.CommonMSDChildCount.body](Directory.definitions.md#def-17306a30d7c126ad)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonStaticSchedule.Instruction](../../../Shared/Programs/Static/Fusion.definitions.md#def-155a585971955476)

**基础库名称**

`List.cons`, `List`, `Nat`

<a id="def-c229910078c8e8d8"></a>
## `CodedSorting.CommonMSDParameters.radix`

下面给出此项的参数类型和完整定义表达式。表达式中使用的项目名称全部列在“继续展开”中；基础库运算见基础概念说明。

[源码位置](Directory.lean#L745)

**类型**

```lean
CodedSorting.CommonSortingNormalization.Configuration → ℕ
```

**定义**

```lean
fun q => q.height / (2 * q.digits)
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration.height](../../Resources/Framework/NormalizationFrames.definitions.md#def-a956e2f48d4f9cd2)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`instHDiv`, `HMul.hMul`, `HDiv.hDiv`, `instMulNat`, `instOfNatNat`, `Nat`, `Nat.instDiv`, `OfNat.ofNat`, `instHMul`

<a id="def-dc8222ade65c70b2"></a>
## `CodedSorting.CommonMSDParameters.radix_two`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Directory.lean#L757)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration), 2 ≤ CodedSorting.CommonMSDParameters.radix q
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](Directory.definitions.md#def-c229910078c8e8d8)

**基础库名称**

`instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`

<a id="def-a41af147cea47d2a"></a>
## `CodedSorting.CommonMSDParameters.directory_fits`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Directory.lean#L767)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration),
  CodedSorting.CommonMSDParameters.radix q * 2 * q.digits ≤ CodedSorting.CommonExchangeLeaf.bankWords q
```

**继续展开**

- [CodedSorting.CommonExchangeLeaf.bankWords](../../../Interchange/Framework/Memory/ExchangeLeaf.definitions.md#def-aaad4ca0dd979eae)
- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)
- [CodedSorting.CommonMSDParameters.radix](Directory.definitions.md#def-c229910078c8e8d8)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `LE.le`, `instLENat`, `Nat`, `OfNat.ofNat`, `instHMul`

<a id="def-6debdfe64b89039a"></a>
## `CodedSorting.CommonMSDChildCount.accWords._proof_2`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Directory.lean)

**类型**

```lean
NeZero (2 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`

<a id="def-91227404ea71bdb1"></a>
## `CodedSorting.CommonMSDChildCount.accWords._proof_3`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Directory.lean)

**类型**

```lean
∀ (q : CodedSorting.CommonSortingNormalization.Configuration) (j : Fin q.digits), ↑j < 13 * q.digits
```

**继续展开**

- [CodedSorting.CommonSortingNormalization.Configuration.digits](../../Resources/Framework/NormalizationFrames.definitions.md#def-c767b1894cb4c907)
- [CodedSorting.CommonSortingNormalization.Configuration](../../Resources/Framework/NormalizationFrames.definitions.md#def-c17122391d7f01c9)

**基础库名称**

`HMul.hMul`, `instMulNat`, `instOfNatNat`, `Fin.val`, `Nat`, `LT.lt`, `instLTNat`, `OfNat.ofNat`, `Fin`, `instHMul`

<a id="def-29d4937227bc9062"></a>
## `CodedSorting.CommonMSDChildCount.addStore._proof_4`

已由 Lean 检查的命题。这里保留它的条件与结论；其中使用的自定义概念继续链接到对应定义。

[源码位置](Directory.lean)

**类型**

```lean
NeZero (1 + 1)
```

此声明没有进一步的项目自定义依赖。

**基础库名称**

`Zero.ofOfNat0`, `instOfNatNat`, `instHAdd`, `HAdd.hAdd`, `Nat`, `instAddNat`, `NeZero`, `OfNat.ofNat`
