import Tensorlayouts.Shape
import Tensorlayouts.ExperimentFunCast

import Mathlib.Data.Set.Basic


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


-- set_option pp.parens true
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


theorem View.is_merge_implies_shape_eq (v v1 v2 : View) (h_merge : View.is_merge v v1 v2) : v.shape = v2.shape := by
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exact Eq.symm hshape


theorem View.is_mergeable_single_dimension_right_implies_linear_function (v1: View) (shape : PosInt) (stride : PosInt) (hshape : shape.val > 1) (v: View) :
  let v2 := View.from_single_dimension shape stride
  let stride' := v1.to_unraveled_index_fn ⟨stride, by sorry ⟩
  (View.is_merge v v1 v2) → v = ({ shape := [shape], stride := [⟨stride', by sorry ⟩], lengthEq := by simp } : View) := by

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
  View.is_mergeable v1 v2 <->
  ( ∃ (hmaxsize : v2.max_index ≤ v1.shape.max_index) (f : LinearIntegerFunc) (h_f : f.max_val = shape.val),
    NatLt.embed_nat ∘ View.compose v1 v2 hmaxsize = f.fun
      ∘ (h_f ▸ (View.from_shape_shape_eq [shape] ▸ @IndexSet.from_single_dimension_equiv shape))) := by
  unfold View.is_mergeable
  unfold View.is_merge






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
    constructor

    . intro h_merge
      obtain ⟨v_merge, hshape, h_merge_fn⟩ := h_merge
      obtain ⟨hmaxsize, h_merge_eq⟩ := h_merge_fn

      have h_v_merge : ∃ (shape stride : PosInt), v_merge = View.from_single_dimension shape stride := by
        sorry

      have hidx_bound : (↑shape - 1) * ↑stride + 1 ≤ v1.shape.max_index := by
        rw [View.from_single_dimension_max_index_eq] at hmaxsize
        exact hmaxsize
      exists hidx_bound

      intros i hi
      sorry
    . sorry





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

Both proofs use the following:



     the linear function from the merged view          =        the composition
           iff

     (1) the first step is equal
     (2) we keep adding the same step


  Better:

  to check that a function (in this case, the composition) is equal to a linear function,
  you can check that the first increment is correct, and that the difference between every two steps is the same as that first increment

  so this is perhaps something we need to prove first


  THIS IS THE MAIN PROBLEM NOW ^^^^
  basically about linear functions with integer steps

-/
