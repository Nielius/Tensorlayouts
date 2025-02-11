import Tensorlayouts.Shape
import Tensorlayouts.ExperimentFunCast
import Tensorlayouts.Merging.Definitions
import Tensorlayouts.Utils

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Nat.Defs



/- ## Merging cons -/

section MergingCons

variable (shape' stride' : PosInt) (v : View) (v1 : View) (shape : PosInt) (stride : PosInt) (v2 : View)


theorem List.head?_getD_eq (l : List α) (h : l ≠ []) (d: α) : l.head?.getD d = l.head h := by
  rw [List.head?_eq_head h]
  rfl

theorem List.headD_eq (l : List α) (h : l ≠ []) (d: α) : l.headD d = l.head h := by
  rw [List.headD_eq_head?_getD]
  apply List.head?_getD_eq

theorem View.cons_to_index_fn_safe_zero (x : IndexSet [shape]) :
  NatLt.embed_nat ((View.cons shape stride v2).index_fn (IndexSet.cons_embed x)) = x.val.head (by sorry) * stride
  := by
  unfold View.index_fn
  unfold IndexSet.cons_embed


  simp [View.cons, View.index_fn, View.index_fn_inner, List.toNats, List.inner_prod, IndexSet.cons_embed, IndexSet.zero]
  conv =>
    lhs
    arg 2
    rw [List.zipWith_map_left]
    enter [1]
    rw [v2.lengthEq]
    rw [List.zipWith_replicate_right]
    simp

  have : ∀ n, (List.replicate n 0).sum = 0 := by
    intro n
    unfold List.sum
    induction n
    case zero =>
      simp
    case succ n ih =>
      rw [List.replicate_succ]
      simp
      assumption

  conv =>
    pattern (List.replicate _ 0).sum
    rw [this (List.length v2.stride)]

  simp [NatLt.embed_nat]
  rw [Nat.mul_comm]
  congr
  rw [List.head?_getD_eq]



theorem View.cons_to_index_fn_safe_zero_as_index_fn  :
  NatLt.embed_nat ∘ (View.cons shape stride v2).index_fn ∘ IndexSet.cons_embed =
  NatLt.embed_nat ∘ (View.from_single_dimension shape stride).index_fn
  := by
  funext x
  have := View.cons_to_index_fn_safe_zero shape stride v2 x
  simp at *
  rw [this]
  rw [View.from_single_dimension_index_fn_safe_eq]
  simp [NatLt.embed_nat]
  congr
  rw [List.head?_getD_eq]


theorem View.cons_to_index_fn_safe_zero_as_index_fn' (x : IndexSet [shape]) :
  ((View.cons shape stride v2).index_fn ∘ IndexSet.cons_embed) x =
  ((View.from_single_dimension shape stride).index_fn x : Nat) := by
  have := congrFun (View.cons_to_index_fn_safe_zero_as_index_fn shape stride v2) x
  simp [NatLt.embed_nat] at *
  assumption


theorem View.cons_max_index_embed_bound :
  (View.from_single_dimension shape stride).max_index ≤ (View.cons shape stride v2).max_index := by
  rw [View.from_single_dimension_max_index_eq]
  rw [View.cons_max_index]
  apply Nat.add_le_add_left
  apply View.max_index_is_positive

theorem View.cons_max_index_embed_bound_tail :
  v2.max_index ≤ (View.cons shape stride v2).max_index := by
  rw [View.cons_max_index]
  rw [Nat.add_comm]
  apply Nat.le_add_right_of_le
  simp



/- Alternative:
theorem View.cons_to_index_fn_safe_zero_as_index_fn''  :
  (View.cons shape stride v2).index_fn ∘ IndexSet.cons_embed =
  NatLt.embedding (View.cons_max_index_embed_bound shape stride v2) ∘ (View.from_single_dimension shape stride).index_fn
-/

theorem View.cons_to_index_fn_safe_zero_as_index_fn''  :
  Subtype.val ∘ (View.cons shape stride v2).index_fn ∘ IndexSet.cons_embed =
  Subtype.val ∘ (View.from_single_dimension shape stride).index_fn
  := by
  funext x
  have := View.cons_to_index_fn_safe_zero shape stride v2 x
  rw [View.from_single_dimension_index_fn_safe_eq]
  simp
  rw [List.head?_getD_eq]
  assumption_mod_cast


theorem View.cons_to_index_fn_safe_zero_as_index_fn_tail  :
  Subtype.val ∘ (View.cons shape stride v2).index_fn ∘ IndexSet.cons_embed_tail =
  Subtype.val ∘ v2.index_fn
  := by
  funext x
  simp [View.cons, View.index_fn, IndexSet.cons_embed_tail]
  unfold View.index_fn_inner
  rw [List.toNats_cons]
  rw [List.inner_prod_cons]
  simp

/-

In mathematics, I'd just write
  (cons_shape shape stride v).index_fn =
  (from_single_dimension shape stride).index_fn + (v.index_fn)
but you need to take care of the embeddings

-/

theorem View.cons_to_index_fn_safe_decomposition (shape stride : PosInt) (v : View) (x : IndexSet (shape :: v.shape)) :
  (Subtype.val ∘ ((View.cons shape stride v).index_fn)) x =
  (Subtype.val ∘ (View.from_single_dimension shape stride).index_fn ∘ Prod.fst ∘ IndexSet.cons_equiv: IndexSet (shape::v.shape) → Nat) x
  + (Subtype.val ∘ v.index_fn ∘ Prod.snd ∘ IndexSet.cons_equiv : IndexSet (shape::v.shape) → Nat) x
  := by
  -- do we need View.cons_shape_eq shape stride v ▸ ?

  /- I want to prove that idx has a head and a tail... -/
  have := (Equiv.left_inv (@IndexSet.cons_equiv shape v.shape)) x
  unfold IndexSet.cons_equiv at this
  dsimp at this
  rw [<- this]

  /- Now simply unfold and use List.inner_prod_cons_as_inner_prods, but we need to be careful with rewrites -/
  simp [View.cons, View.index_fn, View.from_single_dimension]
  rw [<- this]
  simp
  rw [<- this]

  unfold View.index_fn_inner
  rw [List.toNats_cons]
  rw [List.inner_prod_cons_as_inner_prods (α := Nat)]
  simp [List.toNats]


theorem View.compose_cons (v1 : View) (shape stride : PosInt) (v2 : View) (h: (cons shape stride v2).max_index ≤ v1.shape.max_index) :
  Subtype.val ∘ v1.compose (cons shape stride v2) h =
  (fun x => (x.fst + x.snd)) ∘
  (Prod.map
   (Subtype.val ∘ v1.compose (from_single_dimension shape stride) (Nat.le_trans (View.cons_max_index_embed_bound shape stride v2) h))
   (Subtype.val ∘ v1.compose v2                                   (Nat.le_trans (View.cons_max_index_embed_bound_tail shape stride v2) h)))
  ∘ IndexSet.cons_equiv := by
  unfold View.compose

  funext x

  have := View.cons_to_index_fn_safe_decomposition shape stride v2 x
  -- unfold View.to_unraveled_index_fn at *
  unfold View.index_fn at *
  unfold NatLt.embedding
  unfold Subtype.map
  simp at *
  conv =>
    lhs
    enter [1]
    arg 2
    arg 1
    rw [this]

  /- TODO GEBLEVEN
  we basically need to show that to_unraveled_index_fn is additive
  is it?
  -/

  unfold View.to_unraveled_index_fn
  unfold unravel
  unfold View.index_fn
  simp





  norm_cast at this
  conv at this =>
    lhs
    unfold View.index_fn_inner
    simp
    apply Subtype.map
    rw [Subtype.coe]
  simp at this

  conv =>
    lhs
    enter [1]
    pattern ((List.toNats _).inner_prod _)




    rw [this]


  rw [this]





  have := NatLt.embedding_subtype_val_eq_iff_applied.mp this

   ∀ {α : Sort u_1} {a : ℕ} {f : α → { idx // idx < a }} {a_1 : ℕ} {g : α → { idx // idx < a_1 }} {a_2 : ℕ} {h : a ≤ a_2}
  {h' : a_1 ≤ a_2}, Subtype.val ∘ f = Subtype.val ∘ g ↔ NatLt.embedding h ∘ f = NatLt.embedding h' ∘ g

  sorry


/-
 ## GEBLEVEN

- zie de GEBLEVEN van boven
 - use the above theorem to make the proof of View.compose_cons_head/tail easier?
 - or: first prove the same thing for composition
 - then use that to prove the theorem for cons

-/


theorem View.compose_cons (v1 : View) (shape stride : PosInt) (v2 : View) (h: (cons shape stride v2).max_index ≤ v1.shape.max_index) :
  NatLt.embed_nat ∘ (v1.compose (cons shape stride v2) h) ∘ IndexSet.cons_embed
  = NatLt.embed_nat ∘ (v1.compose (from_single_dimension shape stride) (Nat.le_trans (View.cons_max_index_embed_bound shape stride v2) h)) := by
  have h' : (from_single_dimension shape stride).max_index ≤ v1.shape.max_index := by
    rw [View.cons_max_index] at h
    rw [View.from_single_dimension_max_index_eq]
    calc
      (↑shape - 1) * ↑stride + 1 ≤ (↑shape - 1) * ↑stride + v2.max_index := by
        apply Nat.add_le_add_left
        apply View.max_index_is_positive
      _ ≤ v1.shape.max_index := by assumption

  funext x
  unfold View.compose
  repeat rw [Function.comp_assoc]
  unfold NatLt.embed_nat
  simp

  have := congrFun (View.cons_to_index_fn_safe_zero_as_index_fn'' shape stride v2) x
  simp at this
  conv =>
    lhs
    enter [1, 2, 1]
    rw [this]


theorem View.compose_cons_tail (v1 : View) (shape stride : PosInt) (v2 : View) (h: (cons shape stride v2).max_index ≤ v1.shape.max_index) :
  NatLt.embed_nat ∘ (v1.compose (cons shape stride v2) h) ∘ IndexSet.cons_embed_tail
  = NatLt.embed_nat ∘ (v1.compose v2 (Nat.le_trans (View.cons_max_index_embed_bound_tail shape stride v2) h))
  := by
  unfold View.compose
  /- Idea of proof: this basically follows from the analogous statement on index functions-/

  have : NatLt.embedding h ∘ (cons shape stride v2).index_fn ∘ IndexSet.cons_embed_tail =
     NatLt.embedding (Nat.le_trans (View.cons_max_index_embed_bound_tail shape stride v2) h) ∘ v2.index_fn := by
     /- This is just a small rewrite of View.cons_to_index_fn_safe_zero_as_index_fn_tail -/
     have := View.cons_to_index_fn_safe_zero_as_index_fn_tail shape stride v2
     apply NatLt.embedding_subtype_val_eq_iff.mp
     assumption

  repeat rw [Function.comp_assoc]
  rw [this]


/- Is this already in the lib?
   https://github.com/leanprover-community/mathlib4/blob/ee78f4e232bcaca73d4b10671e595ee8111fdfc9/Mathlib/Logic/Basic.lean#L429-L431 -/
theorem cast_heq_iff_heq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :
    HEq (cast e a) c ↔ HEq a c := by subst e; rfl


theorem View.cons_is_merge_cons_for_head :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) →
  (View.from_single_dimension shape' stride').is_merge v1 (View.from_single_dimension shape stride) := by
  -- could add here:
  --  - shape' = shape
  --  - stride' = ....
  -- although maybe it's better to put that in another theorem?

  intro h_merge
  rw [View.is_merge_cast_formulation] at *
  simp at *

  obtain ⟨hshape, hmaxsize, h_total_merge⟩ := h_merge

  obtain ⟨ hshape', _ ⟩ : _ := (View.cons_shape_eq_cons_shape_iff.mp hshape)
  subst hshape'

  have hvshape : v2.shape = v.shape := by
    repeat rw [View.cons_shape_eq] at hshape
    rw [List.cons_eq_cons] at hshape
    obtain ⟨_, hvshape_eq⟩ := hshape
    assumption

  have hshape_eq : (View.from_single_dimension shape stride').shape = (View.from_single_dimension shape stride).shape := by
    rw [View.from_single_dimension_shape_eq]
    rw [View.from_single_dimension_shape_eq]

  exists Eq.symm hshape_eq

  have hmaxsize_head : (View.from_single_dimension shape stride).max_index ≤ v1.shape.max_index := by
    rw [View.cons_max_index] at hmaxsize
    rw [View.from_single_dimension_max_index_eq]
    calc
      (↑shape - 1) * ↑stride + 1 ≤ (↑shape - 1) * ↑stride + v2.max_index := by
        apply Nat.add_le_add_left
        apply View.max_index_is_positive
      _ ≤ v1.shape.max_index := by assumption
  exists hmaxsize_head

  /- Main idea:

  - We have the functional equality from (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2)
  - We precompose this with the equivalence of the index sets; and embed the IndexSet [shape] into the IndexSet (cons shape' stride' v).shape
  - This composition is the merged index function
  -/

  have :          (cons shape stride v2).shape =           shape :: v2.shape := by rw [View.cons_shape_eq]
  have : IndexSet (cons shape stride v2).shape = IndexSet (shape :: v2.shape) := by apply congrArg; assumption
  have h_cons_equiv : IndexSet (cons shape stride v2).shape ≃ IndexSet [shape] × IndexSet v2.shape := by apply IndexSet.cons_equiv

  funext x

  have h_total_merge_embed := congrArg (fun f => (f ∘ IndexSet.cons_embed) x) h_total_merge
  simp at this

  have : cast (congrArg IndexSet hshape) x.cons_embed = x.cons_embed := by
    rw [<- heq_iff_eq]
    rw [cast_heq_iff_heq]
    unfold IndexSet.cons_embed
    congr
    rw [hvshape]
    rw [hvshape]

  simp at h_total_merge_embed
  rw [this] at h_total_merge_embed

  /- Rewrite the index function for v -/
  have := congrFun (View.cons_to_index_fn_safe_zero_as_index_fn shape stride' v) x
  simp at this
  rw [this] at h_total_merge_embed

  /- Rewrite the cons for the composition -/
  have := congrFun (View.compose_cons v1 shape stride v2 hmaxsize) x
  simp [NatLt.embed_nat] at this
  simp [NatLt.embed_nat]
  rw [this] at h_total_merge_embed
  assumption


theorem View.cons_is_merge_cons_for_tail :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) →
  v.is_merge v1 v2 := by

  intro h_merge
  rw [View.is_merge_cast_formulation] at *
  simp at *
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge

  obtain ⟨hshape_eq, hvshape_eq⟩ := View.cons_shape_eq_cons_shape_iff.mp hshape
  subst hshape_eq
  -- subst hvshape_eq -- not possible, because this is an equality of struct attributes

  exists hvshape_eq

  have hmaxsize_tail : v2.max_index ≤ v1.shape.max_index := Nat.le_trans (View.cons_max_index_embed_bound_tail shape stride v2) hmaxsize
  exists hmaxsize_tail

  /- Idea of the proof: from both sides of h_merge_eq, we need to "take the tail"
     The left side is the to_index_fn_safe of the cons (use View.cons_to_index_fn_safe_zero_as_index_fn_tail)
     The right side is v1.compose (cons ...)           (use View.compose_cons_tail)
  -/

  have h_merge_eq_embed := congrArg (fun f => (f ∘ IndexSet.cons_embed_tail)) h_merge_eq
  simp at h_merge_eq_embed
  repeat rw [Function.comp_assoc] at h_merge_eq_embed
  norm_cast at h_merge_eq_embed

  /- Now we have an annoying cast in the way. We need to get rid of it. -/
  have := cast_indexset_eq shape stride v2 shape stride' v hshape
  rw [this] at h_merge_eq_embed

  /- Rewrite the index function -/
  have h_index_fn_eq := View.cons_to_index_fn_safe_zero_as_index_fn_tail shape stride' v
  rw [← NatLt.embed_nat_subtype_val_eq_iff] at h_merge_eq_embed
  conv at h_merge_eq_embed =>
    /- Very annoying: you need to deal with the associativity of function composition to do the appropriate rewrite...-/
    lhs
    repeat rw [Function.comp_assoc]
    repeat rw [<- Function.comp_assoc]
    enter [1]
    repeat rw [Function.comp_assoc]
    rw [h_index_fn_eq]

  /- Rewrite the compose -/
  have h_compose_eq := View.compose_cons_tail v1 shape stride v2 hmaxsize
  rw [<- NatLt.embed_nat_subtype_val_eq_iff] at h_compose_eq
  rw [h_compose_eq] at h_merge_eq_embed

  /- Now done -/
  rw [<- NatLt.embed_nat_subtype_val_eq_iff]
  assumption


theorem View.cons_is_merge_cons (v : View)(v1 : View) (shape : PosInt) (stride : PosInt) (v2 : View) :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) ↔
  v.is_merge v1 v2 ∧ (View.from_single_dimension shape' stride').is_merge v1 (View.from_single_dimension shape stride)
  := by
  constructor

  . intro h_merge
    constructor
    . apply View.cons_is_merge_cons_for_tail
      assumption
    . apply View.cons_is_merge_cons_for_head
      assumption

  . intro h_merge
    obtain ⟨h_merge_head, h_merge_tail⟩ := h_merge



    constructor
    . exact View.cons_is_merge_cons_for_head h_merge
    . exact View.cons_is_merge_cons_for_tail h_merge

end MergingCons
