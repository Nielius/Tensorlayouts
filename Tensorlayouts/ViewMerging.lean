import Tensorlayouts.Shape


/--
  Expresses whether v is a merge of v1 and v2
-/
def View.is_merge (v: View) (v1 : View) (v2 : View) : Prop :=
  exists hshape: v2.shape = v.shape,
  let hshape_fn : (IndexSet v2.shape → Nat) = (IndexSet v.shape → Nat) := by congr
  v.to_index_fn_safe = cast hshape_fn (v1.to_unraveled_index_fn ∘ v2.to_index_fn_safe)

  -- doesn't work: v.to_index_fn_safe == (hshape ▸ (v1.to_unraveled_index_fn ∘ v2.to_index_fn_safe))

def View.is_mergeable  (v1 : View) (v2 : View) : Prop :=
  ∃(v: View), v.is_merge v1 v2


theorem View.is_mergeable_left_canonical (s : Shape) (v2 : View) : View.is_mergeable (View.from_shape s) v2 := by
  exists v2
  unfold View.is_merge
  apply Exists.intro
  swap
  . simp
  .
    simp [View.from_shape]
    unfold View.to_index_fn_safe
    unfold View.to_unraveled_index_fn
    simp
    funext x
    unfold unravel
    unfold unravel_unsafe
    simp








  case w






  unfold View.is_merge



  un


example : View.is_mergeable (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩])) := by
  exists (View.from_shape ([⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩]))
