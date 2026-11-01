# Theorem 3.2: coding and routing

[English](README.md) · [简体中文](README.zh-CN.md)

Network coding lets a node combine information from different sources before sending it. Theorem 3.2 gives a concrete network where this achieves a higher common rate than forwarding messages along paths. The XOR circuit is the same one used by the sorting construction; the [method guide](../../../docs/Idea.md) explains the connection.

[`theorem_3_2`](Theorem.lean) gives a finite simple undirected multiple-unicast network with independent source messages and unit edge capacities such that

$$R_{\mathrm{route}}\le1-\frac{33}{338432}<1=R_{\mathrm{code}}.$$

Each physical edge shares its capacity between the two directions. A finite binary linear code already has rate greater than $1-33/338432$.

## Proof files

| File | Role |
| --- | --- |
| [Coding.lean](Coding.lean) | Network, source–destination pairs, and the concrete coding protocol |
| [Proof.lean](Proof.lean) | Rank bound, routing bound, and the combined result |
| [FiniteCode.lean](FiniteCode.lean) | Finite block lengths and their achieved rates |
| [Theorem.lean](Theorem.lean) | The complete theorem |

The circuit's original streams give the independent messages. Temporary copies carry information used in the computation. The [three-round circuit proof](../../Circuit/Composition/TensorThreeRound.lean) establishes recovery of the original data, and [TensorNetworkGeometry](../../Circuit/Composition/TensorNetworkGeometry.lean) identifies the sessions and their endpoints.

For $k$ bits per session, the code sends successive batches through the network: a new batch enters while earlier batches move onward. This pipeline uses $k+D$ rounds, where $D$ is fixed by the network. The rates $k/(k+D)$ approach $1$. The total capacity leaving a source bounds the rate of every permitted communication protocol by $1$, including binary linear codes. Thus the lower and upper bounds give coding capacity exactly $1$.

Assigning each edge the rank of its endpoint-matrix difference gives a length. Every source-to-destination path must have sufficient total length, which yields the routing upper bound on this same graph. `strictBlock_rate_gt_gap` gives a finite code rate above the explicit numerical bound; `paper_finite_block` provides the block length $\lceil D(1-\eta)/\eta\rceil+1$.

[Network modules](../README.md) · [Models](../../../docs/Model.md) · [Paper guide](../../README.md)
