import Aesop
import Tensorlayouts.ArithHelpers
import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp

/-- ## Shape and Stride -/

def Shape :=  List PosInt
def Stride := List PosInt

deriving instance Repr for Shape
deriving instance Repr for Stride
deriving instance DecidableEq for Shape
deriving instance DecidableEq for Stride
deriving instance Append for Shape
deriving instance Append for Stride

instance : GetElem Shape Nat PosInt (fun s i => i < s.length) where
  getElem s i h := s.get ⟨i, h⟩

instance : GetElem Stride Nat PosInt (fun s i => i < s.length) where
  getElem s i h := s.get ⟨i, h⟩

def Shape.toNats (l : Shape) : List Nat :=
  List.map (fun (x: PosInt) => (x : Nat)) l
def Stride.toNats (l : Stride) : List Nat :=
  List.map (fun (x: PosInt) => (x : Nat)) l

def Stride.from_shape (shape : Shape) : Stride :=
  List.tail (List.scanr (· * ·) ⟨1, by simp⟩ shape)

#eval Stride.from_shape [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨54, by simp⟩]


/-- ## Indexing for shapes -/

def Shape.max_index (shape : Shape) : Nat :=
  Nat.prod shape.toNats

/--
Returns whether an index is valid for a given shape by checking:
1. The index length matches the shape length
2. Each index component is less than the corresponding shape dimension
-/
def Shape.is_valid_index (s : Shape) (idx : List Nat) : Prop :=
  let len_eq := idx.length = s.length
  ∃ (hlen: len_eq),
  ∀ (i : Nat) (h : i < idx.length),
    idx.get ⟨i, h⟩ < s.get ⟨i, by rw [hlen] at h; exact h⟩

/--
The type of valid indices for a given shape
-/
def IndexSet (s : Shape) : Type :=
  {idx : List Nat // Shape.is_valid_index s idx}


/-- ## View -/

structure View where
  shape : Shape
  stride : Stride
  lengthEq : shape.length = stride.length

deriving instance Repr for View
deriving instance DecidableEq for View

def View.mk_unchecked (shape: Shape) (stride : Stride) : Option View :=
  if h : shape.length = stride.length then
    some ⟨shape, stride, h⟩
  else
    none

def View.from_shape_unchecked (shape : Shape) : Option View :=
  View.mk_unchecked shape (Stride.from_shape shape)

def View.from_shape (shape : Shape) : View := {
  shape := shape,
  stride := Stride.from_shape shape,
  lengthEq := by
    unfold Stride.from_shape
    rw [List.scanr_length_tail]
}

theorem View.from_shape_stride_shape_length_eq : ∀ (s: Shape), (List.length s) = (View.from_shape s).stride.length := by
  intro s
  unfold View.from_shape
  unfold Stride.from_shape
  rw [List.scanr_length_tail]

def View.to_index_fn_unsafe (v : View) : List Nat → Option Nat
  | [] => if v.shape.length = 0 then some 0 else none
  | idx => if idx.length = v.shape.length then
            let pairs := List.zip idx v.stride.toNats
            some (List.foldr (fun (p : Nat × Nat) acc => p.1 * p.2 + acc) 0 pairs)
          else
            none

def View.max_index (v : View) : Nat :=
  v.shape.max_index

def View.to_index_fn_safe (v : View) : (IndexSet v.shape) -> Nat :=
  fun ⟨idx, _⟩ => v.stride.toNats.inner_prod idx
  -- we could add here that the result is always less than the max index

example : View :=
  View.from_shape [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨54, by simp⟩]


/-- ## Unraveling -/

def unravel_unsafe (s : Shape) : Nat -> List Nat :=
  fun idx =>
    let view := View.from_shape s
    let shape_and_strides := List.zip s view.stride
    List.map (fun ((shape, stride) : PosInt × PosInt) => (idx / stride) % shape) shape_and_strides


-- TODO: this is not quite correct, because we are taking a modulo at the very last component as well, whereas we shouldn't
def unravel (s : Shape) : Nat -> IndexSet s :=
  fun idx =>
    ⟨ unravel_unsafe s idx, by
      unfold unravel_unsafe
      simp
      unfold Shape.is_valid_index
      simp
      have hlen : min (List.length s) (View.from_shape s).stride.length = List.length s := by
        rewrite [View.from_shape_stride_shape_length_eq]
        simp
      refine ⟨ hlen, ?_ ⟩
      intro i hbound
      apply Nat.mod_lt
      have hi : i < List.length s := by
        rewrite [View.from_shape_stride_shape_length_eq]
        omega
      exact s[i].property
    ⟩

def View.to_unraveled_index_fn (v : View) : Nat -> Nat :=
  v.to_index_fn_safe ∘ unravel v.shape

/--
unravel is the inverse of the index function for the default view for a shape
-/
theorem unravel_correct_other : ∀ (s : Shape) (n : Nat),
  let v := View.from_shape s
  n < v.max_index -> v.to_unraveled_index_fn n = n := by
  intro s n v hbound
  unfold View.to_unraveled_index_fn
  unfold View.to_index_fn_safe
  simp
  unfold View.max_index at hbound
  unfold unravel
  unfold unravel_unsafe
  simp
  simp [View.from_shape]
  induction n
  case zero =>


  case succ n ih =>
    simp
    sorry



  sorry -- this is going to be annoying

theorem unravel_correct_better : ∀ (s : Shape),
  (View.to_index_fn_safe (View.from_shape s)) ∘ unravel s = id := by
  intro s
  funext n
  unfold View.to_index_fn_safe
  unfold View.from_shape
  unfold unravel
  unfold unravel_unsafe
  simp
  sorry -- this might not be correct, because we are taking a modulo at the very last component as well, whereas we shouldn't




theorem unravel_correct : ∀ (s : Shape) (idx : IndexSet s),
  unravel s (View.to_index_fn_safe (View.from_shape s) idx) = idx := by
  intro s idx
  unfold unravel
  unfold unravel_unsafe
  unfold View.to_index_fn_safe
  unfold View.from_shape
  simp
  induction s
  case nil =>
    simp
    sorry -- this is easy
  case cons hd tl ih =>
    simp [ih]
    sorry -- this is going to be annoying

#eval some_example

#check View.to_index_fn_safe some_example


def View.example : View := {
  shape := [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩],
  stride := [⟨12, by simp⟩, ⟨4, by simp⟩, ⟨1, by simp⟩],
  lengthEq := by simp
}
