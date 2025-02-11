import Tensorlayouts.Shape
import Tensorlayouts.ExperimentFunCast
import Tensorlayouts.Merging.Definitions
import Tensorlayouts.Utils

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Nat.Defs


/- ## Casting lemmas -/

theorem cast_indexset_eq__helper (s s' :Shape) (h : s = s') (x : IndexSet s) : x.val = (cast (congrArg IndexSet h) x).val := by
  subst h
  simp


theorem cast_indexset_eq (shape stride : PosInt) (v : View) (shape' stride' : PosInt) (v' : View)
  (h : (View.cons shape stride v).shape = (View.cons shape' stride' v').shape) :
  (cast (congrArg IndexSet h)) ∘ IndexSet.cons_embed_tail =
  IndexSet.cons_embed_tail ∘ (cast (congrArg IndexSet ((View.cons_shape_eq_cons_shape_iff (v := v') (v2 := v)).mp h).right)) := by
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


/- ## Example: left canonical is always mergeable -/

/-- An example of a mergeable view: if the left is canonical, then any view is mergeable with it -/
theorem View.is_mergeable_left_canonical (s : Shape) (v2 : View) (hmaxsize : v2.max_index ≤ s.max_index) :
  View.is_mergeable (View.from_shape s) v2 := by
  exists v2
  unfold View.is_merge
  exists (by rfl)
  exists hmaxsize
  unfold View.compose

  have h_unravel_correct_fn : _ := unravel_correct_fn' s
  rw [h_unravel_correct_fn]

  rfl



/- ## Straight at the target -/


theorem compose_is_linear_if_mergeable
  (v1 v2: View) (h_maxsize : v2.max_index ≤ v1.shape.max_index)
  (h_merge : View.is_mergeable v1 v2)
  (i : IndexFnSet v2.shape)  (j : Fin v2.shape.length) (h : i.val j + 1 < v2.shape.get j):
    (v1.compose v2 h_maxsize (IndexSet.fn_equiv.symm (incrementIndex i j h))).val
  - (v1.compose v2 h_maxsize (IndexSet.fn_equiv.symm i)).val
  = (v1.compose v2 h_maxsize (IndexSet.fn_equiv.symm (incrementIndex (IndexSet.zero v2.shape).fn_equiv j (by sorry)))).val := by
  obtain ⟨v, hv_is_merge⟩ := h_merge
  rw [View.is_merge_cast_formulation] at hv_is_merge
  -- unfold View.is_merge at hv_is_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := hv_is_merge
  unfold NatLt.embed_nat at h_merge_eq

  have := congrFun h_merge_eq (IndexSet.fn_equiv.symm (incrementIndex i j h))
  simp [IndexSet.fn_equiv] at this
  unfold IndexSet.fn_equiv
  simp
  rw [<- this]

  have := congrFun h_merge_eq (IndexSet.fn_equiv.symm i)
  simp [IndexSet.fn_equiv] at this
  rw [<- this]

  have := congrFun h_merge_eq (IndexSet.fn_equiv.symm (incrementIndex (IndexSet.zero v2.shape).fn_equiv j (by sorry)))
  simp [IndexSet.fn_equiv] at this
  rw [<- this]

  cases v with
  | mk vshape vstride vlengthEq =>
    simp at hshape
    subst hshape

    have := View.index_fn_is_linear { shape := v2.shape, stride := vstride, lengthEq := vlengthEq } i j (by sorry)
    simp at this
    simp
    rw [<- this]


theorem mergeability_criterion (v1 v2: View) :
  View.is_mergeable v1 v2 ↔
  -- ∃ (stride : List Nat) (h_stride_len : stride.length = v2.shape.length),
  ∃ (h_composable : v2.max_index ≤ v1.shape.max_index) (stride : Fin v2.shape.length → Nat),
  ∀ (i : IndexFnSet v2.shape) (j : Fin v2.shape.length) (h : i.val j + 1 < v2.shape.get j),
  ((v1.compose v2 h_composable) (IndexSet.fn_equiv.symm (incrementIndex i j h))).val -
  ((v1.compose v2 h_composable) (IndexSet.fn_equiv.symm i)).val = stride j := by
  constructor

  intro h_is_mergeable
  have h_is_mergeable' := h_is_mergeable
  obtain ⟨v, h_is_merge⟩ := h_is_mergeable

  unfold View.is_merge at h_is_merge
  obtain ⟨h_shape, h_maxsize, h_merge_eq⟩ := h_is_merge

  exists h_maxsize

  let i_zero : IndexSet v2.shape := IndexSet.zero v2.shape
  let i_zero_fn : IndexFnSet v2.shape := IndexSet.fn_equiv i_zero
  let stride : Fin (List.length v2.shape) → ℕ := fun j =>
    if h : (v2.shape.get j : Nat) > 1 then
      ((v1.compose v2 h_maxsize) (IndexSet.fn_equiv.symm (incrementIndex i_zero_fn j ?_))).val
      -- Include this if we want offsets  - ((v1.compose v2 h_maxsize) (IndexSet.fn_equiv.symm i_zero_fn)).val
    else 0

  swap -- fill in the hole first
  simp [i_zero_fn, IndexSet.fn_equiv, i_zero, IndexSet.zero]
  exact h.gt

  exists stride
  intro i j h_j

  simp
  have := compose_is_linear_if_mergeable v1 v2 h_maxsize h_is_mergeable' i j h_j

  unfold IndexSet.fn_equiv at this
  simp [IndexSet.fn_equiv] at this
  rw [this]
  unfold stride
  simp

  have h_shape_at_least_2 : 1 < (v2.shape.get j : Nat) := by
     --- (@getElem (List PosInt) ℕ PosInt (fun as i ↦ i < as.length) List.instGetElemNatLtLength v2.shape ↑j j.isLt) : PosInt := by -- (v2.shape[j.val]).val := by
    apply Nat.lt_of_le_of_lt (m := i.val j + 1)
    exact Nat.le_add_left 1 (i.val j)
    assumption

  simp at h_shape_at_least_2
  simp [h_shape_at_least_2]
  rfl

  -- other direction
  intro h_increment_criterion
  obtain ⟨h_composable, stride, h_stride_eq⟩ := h_increment_criterion

  let stride_as_list := List.ofFn stride
  have v_lengthEq : v2.shape.length = List.length stride_as_list := by sorry
  let v : View := { shape := v2.shape, stride := stride_as_list, lengthEq := v_lengthEq }
  exists v

  unfold View.is_merge
  have hshape : v2.shape = v.shape := by unfold v; simp
  exists hshape
  exists h_composable


  simp

  have h_eq_on_fn :
    ∀ (i : IndexFnSet v2.shape),
    (NatLt.embed_nat ∘ Eq.rec (motive := fun x h ↦ IndexSet x → NatLt v.max_index)
       v.index_fn (View.is_merge.proof_2 v v2 hshape)) (IndexSet.fn_equiv.invFun i) =
    (NatLt.embed_nat ∘ v1.compose v2 h_composable) (IndexSet.fn_equiv.invFun i) :=
    by
      apply IndexFnSet.induction
      . have := IndexSet.fn_equiv.left_inv (x := (IndexSet.zero v2.shape))
        rw [this]
        simp
        sorry -- create two lemmas: (1) v.index_fn (IndexSet.zero v2.shape) = 0; (2) v1.compose v2 h_composable (IndexSet.zero v2.shape) = 0
      . intro i j h_j
        simp
        rw [h_stride_eq]
        simp
        rw [h_stride_eq]
        simp



        unfold IndexSet.fn_equiv.toFun




        rw [<- IndexFnSet.zero_equiv]

        simp
        rw [IndexSet.zero_getElem_zero]
        simp




        rw [IndexSet.zero_getElem_zero]
        simp [IndexSet.zero_getElem_zero]




  funext i
  simp

  let i_as_fn : IndexFnSet v2.shape := IndexSet.fn_equiv i
  have h_i_as_fn : i = IndexSet.fn_equiv.invFun i_as_fn := by
    have := IndexSet.fn_equiv.left_inv (α := IndexSet v2.shape)
    unfold Function.LeftInverse at this
    have := (this i).symm
    exact this
  rw [h_i_as_fn]

  apply h_eq_on_fn


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
