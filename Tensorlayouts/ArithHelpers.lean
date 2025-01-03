import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp

def List.inner_prod {α: Type} [Mul α] [Add α] [Zero α] (l : List α) (r : List α) : α :=
   List.sum (List.zipWith (fun x y => x * y) l r)

theorem List.scanr_length {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  List.length (List.scanr f init l) = List.length l + 1 := by
  induction l
  case nil =>
    simp
  case cons hd tl ih =>
    -- apply List.scanr_cons
    rw [List.scanr_cons]
    exact Nat.succ_inj'.mpr ih


theorem List.scanr_length_tail {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  List.length ((List.scanr f init l).tail) = List.length l := by
  simp [List.scanr_length]


theorem List.scanr_head_eq_foldr {α β : Type}  (f : α → β → β) (init : β) (hd : α) (tl : List α) :
  let scanlist := List.scanr f init (hd :: tl)
  ∃ (hnonempty: scanlist ≠ []), List.head scanlist hnonempty = f hd (List.foldr f init tl) := by
  simp

theorem List.scanr_head_eq_foldr_D {α β : Type}  (f : α → β → β) (init : β) (l : List α) :
  let scanlist := List.scanr f init l
  List.headD scanlist init = List.foldr f init l := by
  match l with
  | [] => rfl
  | hd :: tl =>
      intro scanlist
      unfold scanlist
      rw [List.scanr_cons]
      simp
