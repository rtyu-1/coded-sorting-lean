# Paper-to-code guide

[English](README.md) · [简体中文](README.zh-CN.md)

This page maps the numbered results in the paper ([arXiv:2610.20079](https://arxiv.org/abs/2610.20079)) to their Lean 4 source files. The same mapping is available as machine-readable [JSON](paper-map.json).

The proof starts from the [finite linear circuit](Circuit/README.md) in Section 5 and develops two applications:

- **Communication**: turn the circuit into an undirected network with matrix labels and prove a capacity gap between network coding and fractional routing ([Theorem 3.2](NetworkCoding/Theorem32/README.md)).
- **Sorting**: use the same circuit to accelerate [external-memory address-field interchange](Interchange/README.md), then combine local Columnsort with global radix sorting to improve on the comparison-sorting I/O lower bound ([Theorem 3.1](Sorting/Theorem31/README.md)).

## 1. Theorem and lemma index

Each entry file is a starting point for reading the proof; the corresponding construction and bounds may span several modules.

### Main results (Section 3)

| Paper result | Paper title and main conclusion | Lean entry file |
| --- | --- | --- |
| **Theorem 3.1** | **External-memory integer sorting**: Gives a deterministic external-memory integer sorting algorithm that improves on the comparison-sorting bound, with I/O, memory, and polynomial disk-space guarantees. | [Theorem.lean](Sorting/Theorem31/Theorem.lean) |
| **Theorem 3.2** | **A strict coding advantage in undirected multiple-unicast networks**: Constructs an undirected multiple-unicast network with $R_{\mathrm{route}}\le 1-\frac{33}{338432}<1=R_{\mathrm{code}}$. | [Theorem.lean](NetworkCoding/Theorem32/Theorem.lean) |

### Finite linear circuits and the coding counterexample (Section 5 and Appendix B)

| Paper result | Paper title and main conclusion | Lean entry file |
| --- | --- | --- |
| **Lemma 5.1** | **Properties of the local circuit**: Verifies the base XOR circuit with subspace labels in dimension 8: it maps $(x,y,z)\mapsto(x,y+x,z)$ on $v=111$ data-register pairs, restores $R=439$ auxiliary registers, and satisfies the label and temporary-copy cost conditions. | [ConcreteLocalProgram.lean](Circuit/Local/ConcreteLocalProgram.lean) |
| **Lemma 5.2** | **Permutation of the input bits**: The three-round tensor construction in dimension $m=512$ uses three copies sharing auxiliary registers. Each copy swaps its two data groups and restores the auxiliaries, with $W=24{,}432{,}543$ independent inputs in total. | [TensorThreeRound.lean](Circuit/Composition/TensorThreeRound.lean) |
| **Lemma 5.3** | **Total edge length and ranks of source–sink matrix differences**: Computes the sum of edge matrix-difference ranks, $S=12{,}508{,}242{,}237<Wm$, and proves full rank for every source–sink matrix difference, yielding the routing bound and the saving used in the recursion. | [TensorFrameCertifiedBudget.lean](Circuit/Composition/TensorFrameCertifiedBudget.lean) |
| **Corollary 5.4** | **Fixed parameters for the recursion**: Establishes the key recursion inequality $S/W<m^{1-\varepsilon}$, with $\varepsilon=1.5\times10^{-5}$. | [Exponent.lean](Circuit/Parameters/Exponent.lean) |
| **Lemma B.1** | **Parameter inequality**: Uses the first four terms of the exponential series and rational comparisons to prove $\varepsilon\ln m<\eta$, where $\eta=33/338432$, validating the exponent in Corollary 5.4. | [Exponent.lean](Circuit/Parameters/Exponent.lean) |

### Address-field interchange (Section 6 and Appendix C)

| Paper result | Paper title and main conclusion | Lean entry file |
| --- | --- | --- |
| **Lemma 6.1** | **Block transfers for address-field interchange**: Bounds the I/O cost of exchanging two binary address fields of width $u$, with memory and disk-space guarantees for $M\ge\max\{2B,C_{\rm abs}\}$. | [Normalized.lean](Interchange/Binary/Normalized.lean) |
| **Lemma 6.2** | **One level of the coding recursion**: When the prefix count is divisible by $W$, reduces an exchange of width $mf$ to $S$ exchanges of width $f$, each on $V/W$ bits, plus linear scan overhead. | [Exchange.lean](Interchange/OneLevel/Exchange.lean) |
| **Lemma 6.3** | **Interchange for field width $t_0m^k$**: For field width $e=t_0m^k$ and a prefix count divisible by $W^k$, expands the recursion down to short fields and bounds its total I/O cost. | [ConfiguredEndpoint.lean](Interchange/Recursion/ConfiguredEndpoint.lean) |
| **Lemma C.1** | **Interchange for arbitrary field widths and prefix counts**: Moves high digits into the prefix, pads the resulting segments, and splits the remaining fields to extend the recursive exchange bound to arbitrary positive field widths $e$ and prefix counts $P$. | [MachineBound.lean](Interchange/Fields/MachineBound.lean) |

### Local sorting and global radix sorting (Sections 7–8)

| Paper result | Paper title and main conclusion | Lean entry file |
| --- | --- | --- |
| **Proposition 7.1** | **The Columnsort reduction**: For $s=2^t$, $r=s^3$, and $t\ge3$, reduces sorting to four rounds of column sorting, six address-field exchanges, and a constant number of scans, and proves correctness. | [FiniteColumnsort.lean](Sorting/Local/Columnsort/FiniteColumnsort.lean) |
| **Lemma 7.2** | **Local sorting**: Sorts $n\le M^2$ records using a constant number of Columnsort recursion levels, preserving the improved exponent from address exchange. | [CostBound.lean](Sorting/Local/CostBound.lean) |
| **Lemma 8.1** | **Partitioning by one bit group**: Uses local sorting and interval concatenation to partition by one bit group of width at most $\Theta(\log M)$; concatenation after local sorting takes $O(n/B)$ block transfers. | [Complete.lean](Sorting/Radix/Partition/Complete.lean) |
| **Proposition 8.2** | **Sorting large inputs**: Partitions recursively from the most significant bit group downward and sorts small buckets locally, obtaining the global bound for $N\ge M^2$. | [SortingTrace.lean](Sorting/Radix/SortingTrace.lean) |
| **Lemma 8.3** | **A linear number of individual record accesses**: Gives direct radix or counting sort with $O(N)$ I/Os and polynomial disk space for every $M\ge2B$; the main theorem uses it when memory is below a fixed threshold. | [SmallMemorySorting.lean](Sorting/SmallMemory/SmallMemorySorting.lean) |

### Buffered simulation and parameter extension (Appendix A)

| Paper result | Paper title and main conclusion | Lean entry file |
| --- | --- | --- |
| **Lemma A.1** | **Buffered tape simulation**: Buffers tape access with three-block windows, simulating $J$ stages with $T$ total steps on a fixed number of tapes in $O(J+T/(Bw))$ block transfers. | [TapeMachine.lean](Shared/Memory/TapeMachine.lean) |
| **Lemma A.2** | **Constant-factor block simulation**: Shrinks logical blocks and working memory and uses a physical transfer buffer, allowing the algorithms to run when $M/B$ is small, such as $M=2B$, and memory reaches a fixed threshold, with only constant-factor overhead. | [ControlledNormalization.lean](Shared/Programs/ControlledNormalization.lean) |
| **Corollary A.3** | **Extension to general parameters**: Extends the sorting bounds to all legal parameters $2B\le M$, and the address-field exchange bound to $M\ge\max\{2B,C_{\rm abs}\}$, retaining its fixed memory threshold. | [PhysicalRate.lean](Sorting/Radix/PhysicalRate.lean) |

## 2. Paper statements and implementation details

To compose the constructions in Lean 4, the code makes concrete choices about parameters, padding layouts, and the organization of intermediate lemmas. The following table compares those choices with the paper and explains how they support the main theorems.

| Section and detail | Mathematical statement in the paper | Lean implementation and its relation to the paper |
| --- | --- | --- |
| **Section 6.1 and Appendix C: suffix length $l$** | Lemmas 6.1 and C.1 allow any positive integer suffix length $l\ge1$. | The physical execution bounds in Lean apply when $l$ is a multiple of the word width $w$, so each suffix consists of complete machine words. The address exchanges in Sections 7–8 move whole records and satisfy this condition, so this version covers every call in the sorting theorem. |
| **Appendix C: zero padding** | Within each original segment $p\in[P]$, pad its $R$ real subsegments separately to a multiple $R'$ of $W^k$. | Lean combines all real subsegments and pads their total count to the multiple required by the recursion. Under the parameter conditions obtained by borrowing high digits, either layout has less than twice the original data volume. Padding preserves the relative order of real subsegments, and low-field exchanges keep each subsegment's prefix fixed, so removing the padding yields the required exchange on real data in either layout. |
| **Appendix A.3: block-simulation scaling** | Lemma A.2 uses working memory $\widehat M=\lfloor M/4\rfloor$ and logical blocks $\widehat B=\max\{1,\lfloor B/K\rfloor\}$, leaving room for a physical transfer buffer and control information. | Lean uses a fixed reserve constant $C$, with $H=\lfloor M/C\rfloor$ and $b=\max\{1,\lfloor B/C^2\rfloor\}$, to accommodate records, buffers, and control information together. Above the respective fixed memory thresholds, both choices scale memory and block size by fixed factors and preserve the same asymptotic I/O bound. Lemma 8.3 handles sorting below the threshold. |
| **Section 8.3: small-memory disk space** | The compact layout uses $O(N)$ words for counters and linked-list information. Even with one physical block per word, it occupies $O(NB)=O(N^2)$ disk words. | In the branch $w\ge\lceil\log_2N\rceil$, Lean allocates $N+13+6\cdot2^w$ block slots and uses $w=O(\log N)$ to obtain the polynomial word-space bound `smallSpaceBound`. This is looser than the paper's compact layout but meets the polynomial disk-space requirement of Theorem 3.1. |
| **Appendix A.1: multitape simulation** | Lemma A.1 gives a combined bound of $O(J+T/(Bw))$ block transfers for a fixed number of tapes and $J$ stages. | [TapeMachine.lean](Shared/Memory/TapeMachine.lean) proves the three-block-window simulation and transfer bound for one tape; the paper performs the sum over a fixed number of tapes and over stages. The Lean sorting proof directly constructs stream-scan programs and proves the execution and cost of the required transformations in modules including [TriangularProgramBounds.lean](Circuit/Framework/TriangularProgramBounds.lean), establishing the scan overhead needed by the recursion. |

## Related documentation

- **[The sorting theorem explained](../docs/SortingTheorem.md)**: check how the assumptions, conclusion, and computational model of Theorem 3.1 correspond to the Lean statement and its underlying definitions.
- **[Models](../docs/Model.md)**: the external-memory model, word-width conventions, and formal execution control state.
- **[Build and verification](../docs/Verification.md)**: compile the Lean proofs and run the automated checks locally.
