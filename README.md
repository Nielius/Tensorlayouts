# README

## Plans

- special cases of merges
  - if left view is simply canonical view for shape
  - reshapes
    - what does it mean? (define it as a function; both safe and unsafe function)
    - when is it possible? (something about shapes, divisors, etc.)


## TODOs

- use `Fin` from `Mathlib.Data.Fin.Basic` instead of `NatLt`; it is basically the same
- maybe use `Fin n \to Nat` for indices, rather than lists
- coerce or `List.unnatach` instead of `.toNats`?

- how should you use the equivalence? should you use `.toFun` and `.invFun`? I think you probably shouldn't, but sometimes `simp` produces it, and then it's difficult to get rid of, making rewrites that don't involve `.toFun`/`.invFun` difficult