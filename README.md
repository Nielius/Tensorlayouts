# Merging tensor layouts

This repo contains a formal Lean proof of necessary and sufficients conditions for
two tensor views (shade + stride) to be mergeable.
See [this note](doc/problem-formalization.md) for a formal description of this problem, and see [the motivation section](#motivation) for a more intuitive description and information on why we care.
[This pdf](paper/main.pdf) lays out all the mathematical definitions,
and has a proof and an example.

Inspired by a [tinygrad](https://github.com/tinygrad/tinygrad) [bounty](https://github.com/tinygrad/tinygrad/issues/1641).

## Motivation

You can do all kinds of operations on tensors in frameworks like Pytorch or tinygrad: squeeze/unsqueeze, merging/splitting dimensions, transposing, splicing, etc.
For some of these operations, you don't need to change the underlying memory (that could be expensive),
and you can express the result as a "view", defined by a shape and a stride.
However, if you combine these operations in certain ways, you sometimes can not represent the
result as a single view anymore, and you would need to change the memory layout
(or leave the computation implicit/use lazy evaluation; tinygrad uses Shapetrackers to represent
an arbitrary composition of views).
The goal of this repo is to prove in Lean necessary and sufficient conditions for when you can merge two arbitrary views.

See [this explanation](doc/problem-formalization.md) for a more formal description of this problem.

To understand more about strides and shapes in Pytorch (and other frameworks),
see for example
[ezyang's blog on Pytorch internals](http://blog.ezyang.com/2019/05/pytorch-internals/)
or [this other blog post](https://martinlwx.github.io/en/how-to-reprensent-a-tensor-or-ndarray/).


## Statement

For a mathematical treatment, see [this pdf](paper/main.pdf), which has all the definitions, the proofs, and a worked-out example.
That is probably the best place to look if you only care about the mathematics, and not the Lean formalization.

In the Lean code,
the main statement is the theorem `mergeability_criterion` in [`Tensorlayouts.Merging.ViewMerging`](Tensorlayouts/Merging/ViewMerging.lean):

```lean
theorem mergeability_criterion (v1 v2: View) :
  View.is_mergeable v1 v2 ↔
  ∃ (h_composable : v2.max_index ≤ v1.shape.max_index) (stride : Fin v2.shape.length → Nat),
  ∀ (i : IndexFnSet v2.shape) (j : Fin v2.shape.length) (h : i.val j + 1 < v2.shape.get j),
  ((v1.compose v2 h_composable) (IndexSet.fn_equiv.symm (incrementIndex i j h))).val -
  ((v1.compose v2 h_composable) (IndexSet.fn_equiv.symm i)).val = stride j
```

Explanation:

- given a shape `shape`, an object of type `IndexSet shape` represents the set of indices for a tensor of shape `shape`. The indices for a shape $(s_1, \ldots, s_n)$ are $(i_1, \ldots, i_n)$ with $i_j \in \mathbb N$ and $i_j < s_j$ for all $j$. 
- `v1.compose v2` is defined to be the function composition `v1.to_unraveled_index_fn ∘ NatLt.embedding h ∘ v2.index_fn`
  - `v.index_fn` is the function `IndexSet v.shape -> Nat` (actually `IndexSet v.shape -> NatLt v.max_index`) that sends an index to its position in memory. Mathematically, if the view $v$ has shape $(s_1, \ldots, s_n)$ and strides $(\sigma_1, \ldots, \sigma_n)$, then index $(i_1, \ldots, i_n)$ is mapped to $\sum_j \sigma_j i_j$, i.e., the inner product of the strides with the index.
  - `v.to_unraveled_index_fn` is defined as `v.index_fn ∘ unravel v.shape`: it is basically the same as the `index_fn`, except that its domain is `Nat`, and you first need to translate a `Nat` to an index `IndexSet v.shape` in the tensor using `unravel v.shape`.
- informally, the theorem states that two views `v1` and `v2` can be merged if and only if there exists a stride $(\sigma_1, \ldots, \sigma_n)$ such that the function `v1.compose v2 : IndexSet v2.shape -> Nat` increases by exactly $\sigma_j$ whenever you increase the $j$-th component of the index by 1.

Some remarks on this statement:

- this criterion is completely computational: you can easily write a Python function to check it
- however, you need to check quite a lot: for every index in the tensor, you need to check the values after increasing any of the index components
  - an easy way to make this more performant is to do early stopping: if the criterion fails at one index, you can stop; also, there are certain easy cases where you can prove that you don't need to check all indices
- you might be tempted to think that you don't need to check all indices and you can just check e.g. $(0, \ldots, 0)$; see [this example](doc/example-accidental-mergeability.md) to see why that is not true. (The main problem is that you can have "overflows", and depending on the specific sizes and strides, you may miss some overflows, and some overflows may accidentally work out.) You can try to be a bit smarter than checking all indices, but from what I've found, that is going to be very tricky.
- this is a criterion for when you can merge arbitrary views (shape-stride tuples). There might be an cleaner statement if you restrict yourself to certrain kinds of merges that occur more frequently in actual applications (e.g. from doing dimension splits/merges, transposes, splices, etc).

## Current shortcomings

- a few lemmas have not yet been proven, but they should be relatively straightforward to prove
- offsets and masks are not taken into account yet
- lots of checking. From what I can tell, you can try to be smart about not checking everything, but it's quite difficult


## Next steps and todos

- [ ] use Lean's auto-generated docs
- [ ] fill in all the gaps (there are some `sorry`s left)
- [ ] incorporate offsets and masks
- [ ] include theorem on merging more than 2 views (I think the statement will be basically the same: the composition of all functions should still satisfy the requirement when you increase an index component) 
- [ ] add test to tinygrad repo that checks ["accidental mergeability" like this](doc/example-accidental-mergeability.md) .
 
Refactors:

- [ ] use either `IndexSet` or `IndexFnSet`, but not both. E.g. the main theorem uses both...
- [ ] (small) get rid of Experiments.ExperimentFunCast (imported in 2 places, but I don't think it needs to be)
- [ ] use `Fin` from `Mathlib.Data.Fin.Basic` instead of `NatLt`; it is basically the same
- [ ] maybe use `Fin n \to Nat` for indices, rather than lists? We're now using both


## Development

Run `lake build` to check if all relevants files can be built.