import Tensorlayouts.Shape
import Tensorlayouts.ExperimentFunCast
import Tensorlayouts.Utils

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

/- ## Definitions of composing and merging views -/

def View.compose (v1: View) (v2: View) (h: v2.max_index ≤ v1.shape.max_index) : IndexSet v2.shape -> NatLt v1.max_index :=
  v1.to_unraveled_index_fn ∘ NatLt.embedding h ∘ v2.to_index_fn_safe


/--
  Expresses whether v is a merge of v1 and v2
-/
def View.is_merge (v: View) (v1 : View) (v2 : View) : Prop :=
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ (hshape ▸ v.to_index_fn_safe)
  = NatLt.embed_nat ∘ (View.compose v1 v2 hmaxsize)
  -- = NatLt.embed_nat ∘ v1.to_unraveled_index_fn ∘ NatLt.embedding hmaxsize ∘ (cast hshape_fn v2.to_index_fn_safe)


def View.is_mergeable  (v1 : View) (v2 : View) : Prop :=
  ∃(v: View), v.is_merge v1 v2


theorem View.is_merge__helper (v2 v : View) (hshape : v2.shape = v.shape) :
  (hshape ▸ v.to_index_fn_safe) =  v.to_index_fn_safe ∘ (cast (congrArg IndexSet hshape)) := by
  sorry


theorem View.is_merge_cast_formulation (v: View) (v1 : View) (v2 : View)  :
  v.is_merge v1 v2 ↔
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ v.to_index_fn_safe ∘ (cast (congrArg IndexSet hshape))
  = NatLt.embed_nat ∘ (View.compose v1 v2 hmaxsize) := by
  constructor

  /- there is probably a better way to do this; it's basically a rewrite with View.is_merge__helper -/
  intro h_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exists hshape
  exists hmaxsize
  rw [<- View.is_merge__helper v2 v hshape]
  assumption

  intro h_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exists hshape
  exists hmaxsize
  rw [View.is_merge__helper v2 v hshape]
  assumption


theorem cast_indexset_eq__helper (s s' :Shape) (h : s = s') (x : IndexSet s) : x.val = (cast (congrArg IndexSet h) x).val := by
  subst h
  simp



theorem cast_indexset_eq (shape stride : PosInt) (v : View) (shape' stride' : PosInt) (v' : View)
  (h : (View.cons shape stride v).shape = (View.cons shape' stride' v').shape) :
  (cast (congrArg IndexSet h)) ∘ IndexSet.cons_embed_tail =
  IndexSet.cons_embed_tail ∘     (cast (congrArg IndexSet ((View.cons_shape_eq_cons_shape_iff (v := v') (v2 := v)).mp h).right)) := by
  /- afaict, the only reason this is so difficult, is that subst does not work well with structure fields! -/
  funext x
  simp [IndexSet.cons_embed_tail]
  rw [cast_eq_iff_heq]
  rw [Subtype.heq_iff_coe_eq]
  simp
  apply cast_indexset_eq__helper
  exact ((View.cons_shape_eq_cons_shape_iff (v := v') (v2 := v)).mp h).right

  repeat rw [View.cons_shape_eq] at h
  repeat rw [h]
  simp



/- ## Basic theorems about composing and merging views -/

theorem View.is_merge_implies_shape_eq (v v1 v2 : View) (h_merge : View.is_merge v v1 v2) : v.shape = v2.shape := by
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exact Eq.symm hshape


/-- An example of a mergeable view: if the left is canonical, then any view is mergeable with it -/
theorem View.is_mergeable_left_canonical (s : Shape) (v2 : View) (hmaxsize : v2.max_index ≤ s.max_index) :
  View.is_mergeable (View.from_shape s) v2 := by
  exists v2
  unfold View.is_merge
  unfold View.compose

  have hshape : v2.shape = v2.shape := by rfl
  exists hshape
  exists hmaxsize


  have h_unravel_correct_fn : _ := unravel_correct_fn'' s
  obtain ⟨hshape_fn, hcorrect_fn⟩ := h_unravel_correct_fn
  rw [hcorrect_fn]

  have hshape_eq : (from_shape s).shape = s := View.from_shape_shape_eq s
  have hshape_max_index_eq : (from_shape s).shape.max_index = s.max_index := by
    congr

  simp
  have h_cast_comp : _ := NatLt.cast_comp_embedding hmaxsize hshape_fn
  conv =>
    rhs
    arg 2
    rw [<- Function.comp_assoc]
    rw [h_cast_comp]

  rw [<- Function.comp_assoc]
  rw [NatLt.embed_nat_comp_embedding]


/- ## Merging cons -/

section MergingCons

variable (shape' stride' : PosInt) (v : View) (v1 : View) (shape : PosInt) (stride : PosInt) (v2 : View)

theorem View.cons_to_index_fn_safe_zero (x : IndexSet [shape]) :
  NatLt.embed_nat ((View.cons shape stride v2).to_index_fn_safe (IndexSet.cons_embed x)) = x.val.head (by sorry) * stride
  := by
  simp [View.cons, View.to_index_fn_safe, List.toNats, List.inner_prod, IndexSet.cons_embed, IndexSet.zero]
  conv =>
    lhs
    enter [1, 1, 2]
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
  apply Nat.mul_comm

theorem View.cons_to_index_fn_safe_zero_as_index_fn  :
  NatLt.embed_nat ∘ (View.cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed =
  NatLt.embed_nat ∘ (View.from_single_dimension shape stride).to_index_fn_safe
  := by
  funext x
  have := View.cons_to_index_fn_safe_zero shape stride v2 x
  simp at *
  rw [this]
  rw [View.from_single_dimension_index_fn_safe_eq]
  simp [NatLt.embed_nat]


theorem View.cons_to_index_fn_safe_zero_as_index_fn' (x : IndexSet [shape]) :
  ((View.cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed) x =
  ((View.from_single_dimension shape stride).to_index_fn_safe x : Nat) := by
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
  (View.cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed =
  NatLt.embedding (View.cons_max_index_embed_bound shape stride v2) ∘ (View.from_single_dimension shape stride).to_index_fn_safe
-/

theorem View.cons_to_index_fn_safe_zero_as_index_fn''  :
  Subtype.val ∘ (View.cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed =
  Subtype.val ∘ (View.from_single_dimension shape stride).to_index_fn_safe
  := by
  funext x
  have := View.cons_to_index_fn_safe_zero shape stride v2 x
  rw [View.from_single_dimension_index_fn_safe_eq]
  simp
  assumption_mod_cast


theorem View.cons_to_index_fn_safe_zero_as_index_fn_tail  :
  Subtype.val ∘ (View.cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed_tail =
  Subtype.val ∘ v2.to_index_fn_safe
  := by
  funext x
  simp [View.cons, View.to_index_fn_safe, IndexSet.cons_embed_tail]
  rw [List.toNats_cons]
  rw [List.inner_prod_cons]
  simp
  norm_cast


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

  have : NatLt.embedding h ∘ (cons shape stride v2).to_index_fn_safe ∘ IndexSet.cons_embed_tail =
     NatLt.embedding (Nat.le_trans (View.cons_max_index_embed_bound_tail shape stride v2) h) ∘ v2.to_index_fn_safe := by
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


theorem View.is_merge_cons (v : View)(v1 : View) (shape : PosInt) (stride : PosInt) (v2 : View) :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) ↔
  v.is_merge v1 v2 ∧ (View.from_single_dimension shape' stride').is_merge v1 (View.from_single_dimension shape stride)
  := by
  sorry

end MergingCons


/- ## Lemmas about indices -/
section IndexLemmasForTheorem
variable (shape : PosInt) (stride : PosInt) (k : Nat)

theorem lemma_index_stride_in_shape (hidx_bound : (shape - 1) * stride + 1 ≤ k) (i : Nat) (hi : i < shape) : i * stride < k := by
  have hi_shape_minus_one : i ≤ shape - 1 := by omega

  calc
    i * stride ≤ (shape - 1) * stride := by apply Nat.mul_le_mul_right; assumption
    _          < (shape - 1) * stride + 1 := by omega
    _          ≤ k := by assumption

theorem lemma_index_stride_in_shape_first_step (hidx_bound : (shape - 1) * stride + 1 ≤ k) (i : Nat) (hshape : 1 < shape.val) :
  stride < k := by
  rw [← Nat.one_mul ↑stride]
  apply lemma_index_stride_in_shape
  assumption
  omega

theorem lemma_index_in_shape (hidx_bound : shape * stride ≤ k) (i : Nat) :
  i < shape - 1 -> (i + 1) * stride < k
  := by
  intro h

  have h_add : (i + 1) < shape := by
    omega
  have h_mul : (i + 1) * stride < shape * stride := by
    apply Nat.mul_lt_mul_of_pos_right h_add
    exact stride.property

  omega

theorem lemma_index_in_shape' (hidx_bound : shape * stride ≤ k)
 (i : Nat) :
  i < shape - 1 -> i * stride < k
  := by
  intro h
  have hstronger : (i + 1) * stride < k := by
    apply lemma_index_in_shape
    repeat assumption

  have hstride_pos : _ := stride.property
  calc
    i * stride < (i + 1) * stride := by
      apply Nat.mul_lt_mul_of_pos_right
      . simp
      . assumption
    _ < k := by assumption

theorem lemma_index_in_shape'' (hidx_bound : shape * stride ≤ k) (hshape: shape.val > 1) : stride < k := by
  conv =>
    lhs
    rw [← Nat.one_mul ↑stride]
  apply lemma_index_in_shape
  exact hidx_bound
  omega

end IndexLemmasForTheorem


/- ## Relating mergeability to linear functions -/

theorem View.is_mergeable_single_dimension_right_implies_linear_function (v1: View) (shape : PosInt) (stride : PosInt) (hshape : shape.val > 1) (v: View) :
  let v2 := View.from_single_dimension shape stride
  let stride' := v1.to_unraveled_index_fn ⟨stride, by sorry ⟩
  (View.is_merge v v1 v2) → v = View.from_single_dimension shape ⟨stride'.val, by sorry ⟩ := by

  intro v2
  intro stride'
  intro h_merge

  unfold View.is_merge at h_merge

  have hshape_eq : v.shape = v2.shape := by
    apply View.is_merge_implies_shape_eq
    exact h_merge

  /- Useful to do early on: establish v = from_single_dimension vshape vstride, and use that everywhere -/
  have h_v_len_1 : v.shape.length = 1 := by rw [hshape_eq] ; rw [View.from_single_dimension_shape_eq] ; simp
  obtain ⟨ vshape, vstride, hv_eq ⟩ := View.len_1_from_single_dimension v h_v_len_1
  subst hv_eq

  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge

  have hvshape : vshape = shape := by
    repeat rw [View.from_single_dimension_shape_eq] at hshape
    rw [<- List.singleton_inj]
    assumption

  subst hvshape

  /- It remains to do the stride. For that, we need to do a calculation, based on h_merge_eq 1-/
  have h_merge_eq_1 : _ := congrFun h_merge_eq ⟨ [1], by sorry ⟩
  simp at h_merge_eq_1

  /- Left hand side is equal to vstride -/
  rw [View.from_single_dimension_index_fn_safe_eq] at h_merge_eq_1
  simp at h_merge_eq_1

  /- Right hand side is the calculation you get -/
  unfold View.compose at h_merge_eq_1
  simp at h_merge_eq_1
  unfold v2 at h_merge_eq_1
  rw [View.from_single_dimension_index_fn_safe_eq] at h_merge_eq_1
  simp at h_merge_eq_1
  unfold NatLt.embed_nat at h_merge_eq_1
  simp at h_merge_eq_1
  have hvstride : vstride = ⟨stride', by sorry ⟩ := by
    apply Subtype.ext
    assumption

  subst hvstride
  simp [View.from_single_dimension]


theorem View.is_mergeable_single_dimension_right_exists_linear_function (v1: View) (shape : PosInt) (stride : PosInt) (hshape : shape.val > 1) :
  let v2 := View.from_single_dimension shape stride
  View.is_mergeable v1 v2 ↔
  ( ∃ (hmaxsize : v2.max_index ≤ v1.shape.max_index) (f : LinearIntegerFunc) (h_f : f.max_val = shape.val),
    NatLt.embed_nat ∘ View.compose v1 v2 hmaxsize = f.fun
      ∘ (h_f ▸ (View.from_shape_shape_eq [shape] ▸ @IndexSet.from_single_dimension_equiv shape))) := by

  intro v2

  constructor

  . intro h_is_mergeable
    unfold View.is_mergeable at h_is_mergeable
    obtain ⟨v, hv_is_merge⟩ := h_is_mergeable

    let stride' := v1.to_unraveled_index_fn ⟨stride, by sorry ⟩

    have : _ := View.is_mergeable_single_dimension_right_implies_linear_function v1 shape stride hshape v hv_is_merge
    subst this

    unfold View.is_merge at hv_is_merge
    simp at hv_is_merge
    obtain ⟨_ , hmaxsize, h_merge_fun_eq ⟩ := hv_is_merge

    exists hmaxsize
    let f : LinearIntegerFunc := { slope := stride', max_val := ⟨shape , by sorry ⟩}
    exists f
    have h_f : f.max_val = shape.val := by
      simp
    exists h_f
    /- Idea: h_merge_fun_eq shows that is equal to some linear function-/
    rw [View.from_single_dimension_index_fn_safe_linear] at h_merge_fun_eq
    apply Eq.symm
    rw [<- h_merge_fun_eq]

  . intro h_exists
    /- Proof overview:
    - the composition is equal to some linear function
    - from the linear function, we can create a view
    - the index function of the view is the linear function, by construction
    - this shows that it is the merge
    -/
    obtain ⟨hmaxsize, f, h_f, h_merge_fun_eq⟩ := h_exists

    unfold View.is_mergeable
    unfold View.is_merge

    let v := View.from_linear_function f

    exists v

    have hshape : v2.shape = v.shape := by
      rw [View.from_linear_function_shape_eq]
      repeat rw [View.from_single_dimension_shape_eq]
      rw [List.singleton_inj]
      apply Subtype.ext
      rw [h_f]

    exists hshape
    exists hmaxsize
    simp

    rw [<- fun_cast_compose_higher_order]
    unfold v
    rw [View_from_linear_function_to_linear_function]
    rw [h_merge_fun_eq]
    simp
    rw [fun_cast_compose_higher_order]
    apply congrArg (fun x => f.fun ∘ x)
    funext idx
    unfold IndexSet.from_single_dimension_equiv
    simp
    subst_eqs
    simp



theorem View.is_mergeable_multiple_dimensions_reduces_to_single_dimension (v1: View) (v2: View) (shape : PosInt) (stride : PosInt) :
  let v2' : View := View.cons shape stride v2
  View.is_mergeable v1 v2' ↔
  View.is_mergeable v1 v2 ∧ View.is_mergeable v1 (View.from_single_dimension shape stride)
  := by
  constructor
  . intro h_merge
    unfold View.is_mergeable at *
    obtain ⟨v, hv_merge⟩ := h_merge
    unfold View.is_merge at *






theorem View.is_mergeable_single_dimension_right' (v1: View) (shape : PosInt) (stride : PosInt) (hshape : shape.val > 1) :
  View.is_mergeable v1 (View.from_single_dimension shape stride) <->
  ( ∃ (hidx_bound : (shape - 1) * stride + 1 ≤ v1.shape.max_index),
  (∀ (i : Nat) (hi : i < shape - 1),
    -- what do I want to say?
    -- first get the default project
    -- than all next projections, multiplied by the strides,
    -- give the same value
      (v1.to_unraveled_index_fn ⟨ (i + 1) * stride, by apply lemma_index_stride_in_shape ; assumption ; omega ⟩ : Nat)
    = (v1.to_unraveled_index_fn ⟨ i * stride, by apply lemma_index_stride_in_shape; assumption; omega ⟩ : Nat)
    + v1.to_unraveled_index_fn ⟨ stride, by apply lemma_index_stride_in_shape_first_step; repeat assumption ⟩))
    := by

    have : _ := View.is_mergeable_single_dimension_right_exists_linear_function v1 shape stride hshape
    dsimp at this
    rw [this]

    /- Idea of the proof: this is basically an application of LinearIntegerFunc.existence_conditions -/
    sorry





theorem View.is_mergeable_single_dimension_right (v1: View) (shape : PosInt) (stride : PosInt) (hshape : shape.val > 1) :
  View.is_mergeable v1 (View.from_single_dimension shape stride) <->
  ( ∃ (hidx_bound : (shape - 1) * stride + 1 ≤ v1.shape.max_index),
  (∀ (i : Nat) (hi : i < shape - 1),
    -- what do I want to say?
    -- first get the default project
    -- than all next projections, multiplied by the strides,
    -- give the same value
      (v1.to_unraveled_index_fn ⟨ (i + 1) * stride, by apply lemma_index_stride_in_shape ; assumption ; omega ⟩ : Nat)
    = (v1.to_unraveled_index_fn ⟨ i * stride, by apply lemma_index_stride_in_shape; assumption; omega ⟩ : Nat)
    + v1.to_unraveled_index_fn ⟨ stride, by apply lemma_index_stride_in_shape_first_step; repeat assumption ⟩))
    := by
    unfold View.is_mergeable



    constructor

    . intro h_merge

      /-
       The idea of the proof should be this:

       - the merged view looks like [s', σ']
       - the index function hence looks basically linear
       - ....

      -/



      unfold View.is_merge at h_merge
      obtain ⟨v_merge, hshape, h_merge_fn⟩ := h_merge
      obtain ⟨hmaxsize, h_merge_eq⟩ := h_merge_fn

      have hidx_bound : (↑shape - 1) * ↑stride + 1 ≤ v1.shape.max_index := by
        rw [View.from_single_dimension_max_index_eq] at hmaxsize
        exact hmaxsize

      exists hidx_bound
      intros i hi

      have h_v_merge_shape : v_merge.shape = [shape] := by
        rw [<- hshape]
        exact View.from_single_dimension_shape_eq shape stride

      -- This is what we want to use:
      -- IndexSet v_merge.shape = IndexSet [shape] = NatLt shape
      -- and then show that i is in there

      let i_as_index_for_proof : IndexSet [shape] :=
         IndexSet.from_single_dimension_equiv.invFun ⟨i, by omega⟩
         -- h_v_merge_shape ▸ (IndexSet.from_single_dimension_equiv.invFun ⟨i, by omega⟩)

      let i_as_index : IndexSet v_merge.shape :=
        ⟨ [i], by rw [<- hshape] ; exact i_as_index_for_proof.property ⟩


      -- have i_as_natlt : NatLt shape := ⟨i, by omega⟩
      -- have i_as_index : IndexSet [shape] := IndexSet.from_single_dimension_equiv.invFun i_as_natlt
      -- have i_as_index_v_merge : IndexSet v_merge.shape := h_v_merge_shape ▸ i_as_index

      -- have i_as_index_v_merge' : IndexSet v_merge.shape := ⟨[i], by
      --   exact i_as_index_v_merge.property
      -- ⟩

      have h_merge_eq_i := congrFun h_merge_eq ⟨ [i], by rw [<- hshape] ; exact i_as_index_for_proof.property ⟩

      rw [View.from_single_dimension_index_fn_safe_eq] at h_merge_eq_i
      simp at h_merge_eq_i



      simp [View.from_single_dimension, View.to_index_fn_safe, View.to_unraveled_index_fn] at h_merge_eq_i
      simp [View.to_index_fn_safe, List.toNats, List.inner_prod, List.map, List.zipWith] at h_merge_eq_i

      have h_index_fn_eq : v.to_index_fn_safe =
        cast (by rw [hv_eq]) (from_single_dimension vshape vstride).to_index_fn_safe := by
        rw [hv_eq]

      have h_compose_eq : NatLt.embed_nat ∘ v.to_index_fn_safe =
        NatLt.embed_nat ∘ (cast (by rw [hv_eq]) (from_single_dimension vshape vstride).to_index_fn_safe) := by
        congr
        exact h_index_fn_eq

      sorry

    . /-

      idea of proof:

      - set the merged view to [s' = s, σ'], where σ' comes from the first projection that we take

      -/
      sorry

/-


/- Theorems that are next:


1. Overflows: express the equality conditions by only looking at the overflows, giving equations on the strides
2. v2 with length > 1
3. composing several views?

-/
