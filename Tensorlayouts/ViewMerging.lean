import Tensorlayouts.Shape

import Mathlib.Data.Set.Basic

/--
  Expresses whether v is a merge of v1 and v2
-/
def View.is_merge (v: View) (v1 : View) (v2 : View) : Prop :=
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ v.to_index_fn_safe
  = NatLt.embed_nat ∘ v1.to_unraveled_index_fn ∘ NatLt.embedding hmaxsize ∘ (cast hshape_fn v2.to_index_fn_safe)


def View.is_mergeable  (v1 : View) (v2 : View) : Prop :=
  ∃(v: View), v.is_merge v1 v2


-- set_option pp.parens true
theorem View.is_mergeable_left_canonical (s : Shape) (v2 : View) (hmaxsize : v2.max_index ≤ s.max_index) :
  View.is_mergeable (View.from_shape s) v2 := by
  exists v2
  unfold View.is_merge

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


example : View.is_mergeable (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) := by
  exists (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩]))
