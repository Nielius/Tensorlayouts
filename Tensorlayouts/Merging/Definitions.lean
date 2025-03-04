import Tensorlayouts.Shape
import Tensorlayouts.Experiments.ExperimentFunCast
import Tensorlayouts.View


/- ## Definitions of composing and merging views -/

def View.compose (v1: View) (v2: View) (h: v2.max_index ≤ v1.shape.max_index) : IndexSet v2.shape -> NatLt v1.max_index :=
  v1.to_unraveled_index_fn ∘ NatLt.embedding h ∘ v2.index_fn

/--
  Expresses whether v is a merge of v1 and v2
-/
def View.is_merge (v: View) (v1 : View) (v2 : View) : Prop :=
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ (hshape ▸ v.index_fn)
  = NatLt.embed_nat ∘ (View.compose v1 v2 hmaxsize)
  -- = NatLt.embed_nat ∘ v1.to_unraveled_index_fn ∘ NatLt.embedding hmaxsize ∘ (cast hshape_fn v2.index_fn)


def View.is_mergeable  (v1 : View) (v2 : View) : Prop :=
  ∃(v: View), v.is_merge v1 v2



/- ## Alternative formulation of View.is_merge -/

theorem View.is_merge_cast_formulation (v: View) (v1 : View) (v2 : View)  :
  v.is_merge v1 v2 ↔
  exists (hshape: v2.shape = v.shape)
         (hmaxsize : v2.max_index ≤ v1.shape.max_index),
  let hshape_fn :  (IndexSet v2.shape → NatLt v2.max_index) = (IndexSet v.shape → NatLt v2.max_index) := by congr
    NatLt.embed_nat ∘ v.index_fn ∘ (cast (congrArg IndexSet hshape))
  = NatLt.embed_nat ∘ (View.compose v1 v2 hmaxsize) := by
  constructor

  /- there is probably a better way to do this; it's basically a rewrite -/
  intro h_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exists hshape
  exists hmaxsize

  rw [<- fun_cast_input_move_to_input_composition v.index_fn hshape.symm]
  assumption

  intro h_merge
  obtain ⟨hshape, hmaxsize, h_merge_eq⟩ := h_merge
  exists hshape
  exists hmaxsize
  rw [fun_cast_input_move_to_input_composition v.index_fn hshape.symm]
  assumption
