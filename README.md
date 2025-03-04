# Merging tensor layouts

This repo contains a formal Lean proof of necessary and sufficients conditions for
two tensor views (shade + stride) to be mergeable. See [this note](doc/problem-formalization.md) for a formal description of this problem, and see [the motivation section](#motivation) for a more intuitive description and information on why we care.

Inspired by a [tinygrad](https://github.com/tinygrad/tinygrad) [bounty](https://github.com/tinygrad/tinygrad/issues/1641).

## Motivation

TODO (main reason: no need to rearrange memory)

## Statement

This is

## Current shortcomings

- a few lemmas have not yet been proven, but they should be relatively straightforward to prove
- offsets and masks are not taken into account yet
- lots of checking. From what I can tell, you can try to be smart about not checking everything, but it's quite difficult


## Plans

- special cases of merges
  - if left view is simply canonical view for shape
  - reshapes
    - what does it mean? (define it as a function; both safe and unsafe function)
    - when is it possible? (something about shapes, divisors, etc.)


## Next steps and todos

- [ ] fill in all the gaps (there are some `sorry`s left)
- [ ] incorporate offsets and masks
- [ ] include theorem on merging more than 2 views (I think the statement will be basically the same: the composition of all functions should still satisfy the requirement when you increase an index component) 
- possible refactors
  - [ ] use `Fin` from `Mathlib.Data.Fin.Basic` instead of `NatLt`; it is basically the same
  - [ ] maybe use `Fin n \to Nat` for indices, rather than lists? We're now using both

- how should you use the equivalence? should you use `.toFun` and `.invFun`? I think you probably shouldn't, but sometimes `simp` produces it, and then it's difficult to get rid of, making rewrites that don't involve `.toFun`/`.invFun` difficult
  - I think I should try to stick to the version without `.toFun` and `.invFun`