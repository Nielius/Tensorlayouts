import Tensorlayouts.Shape
import Tensorlayouts.Experiments.ExperimentFunCast
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


theorem View.compose_is_increasing (v1 v2 : View) (h_maxsize : v2.max_index ≤ v1.shape.max_index)
  (i : IndexFnSet v2.shape)  (j : Fin v2.shape.length) (h : i.val j + 1 < v2.shape.get j) :
    (v1.compose v2 h_maxsize (IndexSet.fn_equiv.symm (incrementIndex i j h))).val
  ≥ (v1.compose v2 h_maxsize (IndexSet.fn_equiv.symm i)).val := by
  sorry

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
    simp [IndexSet.fn_equiv] at this
    simp [IndexSet.fn_equiv]
    rw [<- this]


theorem mergeability_criterion (v1 v2: View) :
  View.is_mergeable v1 v2 ↔
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

  simp [IndexSet.fn_equiv]
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
       v.index_fn (View.is_merge.proof_2 v v2 hshape)) (IndexSet.fn_equiv.symm i) =
    (NatLt.embed_nat ∘ v1.compose v2 h_composable) (IndexSet.fn_equiv.symm i) :=
    by
      apply IndexFnSet.induction
      . simp
        sorry -- create two lemmas: (1) v.index_fn (IndexSet.zero v2.shape) = 0; (2) v1.compose v2 h_composable (IndexSet.zero v2.shape) = 0
      . intro i j h_j ih
        simp

        -- need to get rid of: v2.shape = v.shape, because then we get rid of annoying casts
        unfold v
        unfold v at ih
        simp at ih
        simp only [Function.comp_apply, NatLt.embed_nat_coe]

        -- rewrite the left hand side: basically index_fn(i) + stride(j)
        simp [View.index_fn_step_is_stride]

        -- rewrite the right hand side: basically v1.compose v2 h_composable (IndexSet.fn_equiv.symm i) + stride j
        have : ↑(v1.compose v2 h_composable (IndexSet.fn_equiv.symm (incrementIndex i j h_j)))
             = ↑(v1.compose v2 h_composable (IndexSet.fn_equiv.symm i)) + stride j := by
          rw [<- Nat.sub_eq_iff_eq_add']
          rw [h_stride_eq]
          apply View.compose_is_increasing
        rw [this]

        -- now conclude by rewriting with the induction hypothesis
        rw [ih]
        unfold stride_as_list
        simp

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



/-
TODO:

theorem mergeability_criterion' where we use that we already know what the stride has to be;
[a-soulspark also explained this](https://github.com/tinygrad/tinygrad/issues/8511#issuecomment-2573239894).
We can just plug in the value of the strides in theorem mergeability_criterion.

-/
