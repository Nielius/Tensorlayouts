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



set_option pp.proofs true
set_option pp.coercions true
-- pp.deepTerms



theorem View.is_merge_cons_as_cons_of_head :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) →
  (View.from_single_dimension shape' stride').is_merge v1 (View.from_single_dimension shape stride) := by

  intro h_merge
  unfold View.is_merge at h_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge

  /- Try to change the annoying Eq.rec-/

  dsimp at h_merge_eq
  conv at h_merge_eq =>
    lhs
    rw [← fun_cast_compose_higher_order]


  have hshape' : shape = shape' := by
    repeat rw [View.cons_shape_eq] at hshape
    rw [List.cons_eq_cons] at hshape
    obtain ⟨hshape_eq, _⟩ := hshape
    assumption
  subst hshape'

  have hvshape : v2.shape = v.shape := by
    repeat rw [View.cons_shape_eq] at hshape
    rw [List.cons_eq_cons] at hshape
    obtain ⟨_, hvshape_eq⟩ := hshape
    assumption


  have hshape_eq : (View.from_single_dimension shape stride').shape = (View.from_single_dimension shape stride).shape := by
    rw [View.from_single_dimension_shape_eq]
    rw [View.from_single_dimension_shape_eq]
    repeat rw [View.cons_shape_eq] at hshape

  unfold View.is_merge
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

  have := congrArg (fun x => x ∘ IndexSet.cons_embed) h_merge_eq
  simp at this

  funext x


  have h_merge_eq_applied := congrFun this x
  unfold View.compose at h_merge_eq_applied
  repeat rw [Function.comp_assoc] at h_merge_eq_applied

  simp at h_merge_eq_applied

  unfold NatLt.embed_nat at *
  simp at *

  have h_cons_embed_eq : _ := congrFun (View.cons_to_index_fn_safe_zero_as_index_fn shape stride v2) x
  simp [NatLt.embed_nat] at h_cons_embed_eq
  have h_cons_embed_eq' : _ := congrFun (View.cons_to_index_fn_safe_zero_as_index_fn shape stride' v) x
  simp [NatLt.embed_nat] at h_cons_embed_eq'

  conv at h_merge_eq_applied =>
    pattern (v1.to_unraveled_index_fn _)
    enter [2, 1]
    rw [h_cons_embed_eq]

  -- simp [hvshape] at h_merge_eq_applied
  /- change the location of the cast -/
  conv at h_merge_eq_applied =>
    lhs
    rw [fun_cast_input_move_to_input]
    unfold Function.comp
    arg 1
    simp

  simp at h_merge_eq_applied


  have : ((cons shape stride' v).to_index_fn_safe x.cons_embed) =
     (cons shape stride' v).to_index_fn_safe (@Eq.rec Shape (cons shape stride v2).shape (fun x h ↦ IndexSet x) x.cons_embed (cons shape stride' v).shape
     (Eq.symm (is_merge.proof_2 (cons shape stride' v) (cons shape stride v2) hshape))) := by

     have : HEq (@IndexSet.cons_embed shape v.shape x : IndexSet (shape :: v.shape)) (@IndexSet.cons_embed shape v2.shape x : IndexSet (shape :: v2.shape)) := by
      unfold IndexSet.cons_embed
      rw [hvshape]

     apply congrArg
     rw [<- heq_iff_eq]
     rw [heq_rec_iff_heq]
     assumption

  -- GEBLEVEN

  rw [this] at h_merge_eq_applied

  have : (@Eq.rec Shape (cons shape stride v2).shape (fun x h ↦ IndexSet x) (@IndexSet.cons_embed shape v2.shape x) (cons shape stride' v).shape) = @IndexSet.cons_embed shape v.shape x := by
    simp
  subst_eqs

  change v2.shape with v.shape at h_merge_eq_applied
  change x.cons_embed with v.shape at h_merge_eq_applied

  simp at h_merge_eq_applied
  subst_eqs




  have : (is_merge.proof_2 (cons shape stride' v) (cons shape stride v2) hshape) ▸ x.cons_embed
     = x.cons_embed := by


  -- have : ((Eq.symm (is_merge.proof_2 (cons shape stride' v) (cons shape stride v2) hshape) : (cons shape stride v2).shape = (cons shape stride' v).shape) ▸ x.cons_embed)




















theorem View.is_merge_cons_as_cons_of_tail :
  (View.cons shape' stride' v).is_merge v1 (View.cons shape stride v2) →
  v.is_merge v1 v2 :=
  by sorry





theorem View.is_merge_cons (v : View)(v1 : View) (shape : PosInt) (stride : PosInt) (v2 : View) :
  v.is_merge v1 (View.cons shape stride v2) →
  View.is_merge v1 v2 ∧ View.is_merge v1 (View.from_single_dimension shape stride)
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
