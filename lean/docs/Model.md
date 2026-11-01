# Models

[English](Model.md) · [简体中文](Model.zh-CN.md)

The sorting result counts data transfers between disk and memory. The network result compares communication rates on the same graph. This page specifies the inputs, operations, and resources for both processes.

## External-memory sorting

The input consists of $N$ integers stored consecutively on disk. Each integer occupies one $w$-bit machine word. Memory holds $M$ words and each disk block contains $B$ words, with $N\ge2$, $B>0$, and $2B\le M\le N$.

**Block transfers.** Reading or writing one disk block costs one I/O. Computation on data already in memory costs zero I/Os. Buffers, counters, pointers, and working data occupy storage under the execution convention below. The [normal-memory](SortingTheorem.md#22-check-2-execution-and-physical-io-accounting) and [small-memory](SortingTheorem.md#32-check-2-small-memory-execution-and-io-accounting) execution sections of the sorting theorem guide expand the physical transfers and their I/O charges.

**Word width.** Fixed constants $c,\kappa$ relate word width to input size:

$$\lceil\log_2N\rceil\le cw,\qquad w\ln2\le\kappa\ln N.$$

Together these inequalities express $w=\Theta(\log N)$. [WordConvention.Covers](../CodedSorting/Shared/Words/WordConvention.lean) defines the lower bound. Addresses bounded by a fixed polynomial in $N$ therefore occupy a constant number of words. The complexity analysis fixes $c,\kappa$ before varying the input size and machine parameters.

**Programs and execution position.** The size parameters determine a program that serves every input of that size. Program code is stored separately from data memory. Recursive sorting keeps the current call's control variables in memory and writes suspended parent calls to disk. The small-memory algorithm uses two block buffers. Its $w<\lceil\log_2N\rceil$ case runs a predetermined instruction sequence whose position is maintained by program control outside the $M$ data words. Other mutable working data is accounted for in memory or on disk.

**Output and space.** The execution terminates with a nondecreasing disk file preserving every input value and its multiplicity. The theorem also bounds resident storage by $M$ words, disk space by a polynomial, and the I/O count by the sorting formula. [NormalGuarantee and SmallGuarantee](../CodedSorting/Sorting/Theorem31/Proof.lean) specify these conclusions for recursive and small-memory sorting.

## Undirected multiple-unicast communication

The network is a finite simple undirected graph. Each edge has capacity $1$, shared between its two directions. There are multiple unicast sessions, each with a source and a destination. Each source holds a binary message that its destination must recover; messages from different sessions are mutually independent.

**Coding protocols.** A protocol specifies when an edge transmits and in which direction. Nodes compute outgoing messages from their state and previously received information. The construction uses linear maps over the binary field $\mathbb F_2$ for initialization, transmission, state updates, and decoding. See [BlockCode](../CodedSorting/NetworkCoding/Model/NetworkRates.lean) and [BinaryLinearBlock](../CodedSorting/NetworkCoding/FiniteCodes/BinaryLinearPipeline.lean).

**Communication rate.** Sending $k$ bits per session in $T$ rounds gives common rate $k/T$. The construction is pipelined: a new batch enters while earlier batches move through the network. It takes $k+D$ rounds, where the fixed delay $D$ depends on the network, so the rate approaches $1$ as $k$ increases. A capacity constraint at a source gives the upper bound $1$, establishing coding capacity exactly $1$.

**Fractional routing.** A session can divide its flow among several source-to-destination paths. The load on an edge includes every session and both directions. On this same graph, routing capacity is at most $1-33/338432$. The [method guide](Idea.md) explains the path-length argument.
