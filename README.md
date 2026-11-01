# Coded Sorting

[English](README.md) · [简体中文](README.zh-CN.md)

This repository provides the Lean 4 formalization of **Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting**, by Baochun Li, Zongpeng Li, and Sirui Liu ([preprint](https://arxiv.org/abs/2610.20079)).

The paper constructs an undirected multiple-unicast network in which network coding achieves rates strictly above those achievable by fractional routing, giving a counterexample to the multiple-unicast conjecture proposed in 2004. It also uses the linear structure of this construction to accelerate external-memory data rearrangement, surpassing the comparison-based sorting input/output (I/O) lower bound and answering the open question raised by Aggarwal and Vitter in 1988.

## Method

A substantial part of the block-transfer cost of external-memory sorting comes from fixed rearrangements of data positions. The paper turns the communication advantage of network coding into faster sorting in three steps:

1. **Finite linear circuit and coding counterexample.** Construct a finite XOR circuit acting on multiple data streams. Turning its connections into undirected network edges gives a coding scheme with a rate strictly above the fractional-routing upper bound.
2. **Faster address-field exchange using the circuit.** Divide the array into equal-length streams and feed them into the circuit. By combining and recovering data through XOR, reduce an exchange of long address fields to exchanges of shorter fields, with the subtasks processing strictly less total data than direct pair-by-pair exchange. Applying this reduction recursively decreases the block transfers needed for rearrangement; the [method guide](lean/docs/Idea.md) gives the calculation.
3. **From fixed rearrangement to external-memory sorting.** Use the faster address-field exchange to implement Columnsort's fixed rearrangements between columns. A constant number of recursive levels sorts arrays of size at most $M^2$; radix sorting by leading digits then extends the algorithm to arbitrary input size $N$.

## Results

**External-memory integer sorting.** Suppose the disk holds $N\ge2$ integers of width $w=\Theta(\log N)$ bits, memory holds $M$ words, and each block transfer moves $B$ words, with $2B\le M\le N$. The paper gives a deterministic algorithm that uses at most $M$ memory words and polynomial disk space and sorts the input in

$$O\left(\frac NB\left[1+\frac{\log N}{(\log(M/B))^{1-\varepsilon}(\log M)^\varepsilon}\right]\right),\qquad \varepsilon=1.5\times10^{-5},$$

block transfers. The improvement is particularly clear when memory holds only a few disk blocks: for $M=2B$ and $N=B^2$, comparison sorting requires $\Theta(B\log B)$ I/Os, whereas this algorithm uses $O(B(\log B)^{1-\varepsilon})$. The algorithm works for every input, including repeated values; the [model guide](lean/docs/Model.md) gives the complete model and execution-control conventions.

**Undirected multiple-unicast network coding.** The circuit construction gives a finite simple undirected multiple-unicast network with unit edge capacities shared between both directions, in which the binary linear network coding capacity $R_{\mathrm{code}}$ is strictly greater than the fractional routing capacity $R_{\mathrm{route}}$:

$$R_{\mathrm{route}}\le1-\frac{33}{338432}<1=R_{\mathrm{code}}.$$

This repository formally verifies both main results in Lean 4. The [paper-to-code guide](lean/CodedSorting/README.md) links each theorem and lemma to its implementation.

## Reading guide

Start with [Algorithm Overview](lean/docs/Idea.md) to understand how rearrangement accelerates sorting and how it connects to the network coding counterexample. Then read [The sorting theorem explained](lean/docs/SortingTheorem.md) to check that the sorting theorem's assumptions, conclusion, and computational model match the Lean statement and its underlying definitions.

To find a particular proof, use the [paper-to-code guide](lean/CodedSorting/README.md) to look up theorem and lemma numbers, or follow the [source layout](lean/docs/Structure.md) to browse the implementation by module.

## Build the proofs

Install the [Lean toolchain manager](https://lean-lang.org/install/), Git, and Python 3. Download the repository, then run these commands from its root:

```sh
cd lean
lake exe cache get
python3 scripts/verify.py
```

The project pins **Lean 4.19.0** and the Mathlib revision in its dependency manifest. The verification command compiles the proofs, checks the main theorem statements and their axiom dependencies, and writes results to `lean/reports/`. See [build and verification](lean/docs/Verification.md) for setup, output files, and GitHub Actions.

## Contribute and cite

See [CONTRIBUTING.md](CONTRIBUTING.md) for contributions and [CITATION.cff](CITATION.cff) for citation metadata. The code uses the [MIT license](LICENSE).
