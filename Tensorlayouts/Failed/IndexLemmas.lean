import Tensorlayouts.Shape
import Tensorlayouts.Experiments.ExperimentFunCast
import Tensorlayouts.Merging.Definitions
import Tensorlayouts.Utils

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Nat.Defs


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



      simp [View.from_single_dimension, View.index_fn, View.to_unraveled_index_fn] at h_merge_eq_i
      simp [View.index_fn, List.toNats, List.inner_prod, List.map, List.zipWith] at h_merge_eq_i

      have h_index_fn_eq : v.index_fn =
        cast (by rw [hv_eq]) (from_single_dimension vshape vstride).index_fn := by
        rw [hv_eq]

      have h_compose_eq : NatLt.embed_nat ∘ v.index_fn =
        NatLt.embed_nat ∘ (cast (by rw [hv_eq]) (from_single_dimension vshape vstride).index_fn) := by
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
