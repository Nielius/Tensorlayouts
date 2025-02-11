import Tensorlayouts.Shape

structure ShapeTracker where
  views : List View

def ShapeTracker.compose (st: ShapeTracker) (view : View) : ShapeTracker := {
  views := st.views ++ [view]
}

def ShapeTracker.compose_many (st: ShapeTracker) (views : List View) : ShapeTracker := {
  views := st.views ++ views
}


def ShapeTracker.to_index_fn (st: ShapeTracker) : List Nat -> Nat :=
  fun idx =>
    let view_fns := st.views.map View.to_unraveled_index_fn
    let pairs := List.zip idx last_view.stride
    List.foldr (fun (p : Nat × Nat) acc => p.1 * p.2 + acc) 0 pairs


def ShapeTracker.index_fn (st: ShapeTracker) : IndexSet st.views.getLastD.shape -> Nat :=
  fun ⟨idx, _⟩ =>
  let pairs := List.zip idx st.views.map View.stride
  List.foldr (fun (p : Nat × Nat) acc => p.1 * p.2 + acc) 0 pairs
