import Aesop
import Tensorlayouts.ArithHelpers
import Tensorlayouts.CastingLemmas
import Tensorlayouts.LinearIntegerFunc
import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp
import Mathlib.Data.List.Zip -- needed for List.zipWith_map_right
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.OfFn

/- ## Shape and Stride -/

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

def List.toNats (l : List PosInt) : List Nat :=
  List.map (fun (x: PosInt) => (x : Nat)) l

theorem List.toNats_length (l : List PosInt) : List.length (List.toNats l) = List.length l := by
  unfold List.toNats
  simp

theorem List.toNats_getElem (l : List PosInt) (i : Nat) (h : i < List.length l) :
  (List.toNats l).get ⟨i, (List.toNats_length l) ▸ h⟩ = l.get ⟨i, h⟩ := by
  unfold List.toNats
  simp

theorem List.toNats_nil : List.toNats [] = [] := by
  unfold List.toNats
  simp

theorem List.toNats_cons (hd : PosInt) (tl : List PosInt)  :
  List.toNats (hd :: tl) = (hd : Nat) :: List.toNats tl := by
  unfold List.toNats
  simp

def Stride.from_shape (shape : Shape) : Stride :=
  List.tail (List.scanr (· * ·) ⟨1, by simp⟩ shape)

def Stride.from_shape_nil : Stride.from_shape [] = [] := by
  unfold Stride.from_shape
  rw [List.scanr_nil]
  simp

def Stride.from_shape_cons (hd : PosInt) (tl : List PosInt) :
  Stride.from_shape (hd :: tl) =
    let stride_tail := Stride.from_shape tl
    (tl.headD ⟨1, by simp⟩ * stride_tail.headD ⟨1, by simp⟩) :: stride_tail := by
  unfold Stride.from_shape
  rw [List.scanr_cons_as_cons_scanr]
  simp

  induction tl
  case nil =>
    simp
    unfold HMul.hMul
    unfold instHMulPosInt
    simp
  case cons hd' tl' ih =>
    rw [List.scanr_cons_as_cons_scanr]
    simp
    congr
    apply List.head?_eq_getElem?


/- ## Indexing for shapes -/

/--
 Strict upper bound for the index that the shape can represent
 in the shape's canonical view.
 'Strict' means strict inequality, i.e. idx < shape.max_index
-/
def Shape.max_index (shape : Shape) : Nat :=
  Nat.prod shape.toNats

theorem Shape.max_index_cons (a : PosInt) (shape : Shape) :
  Shape.max_index (a :: shape) = a * Shape.max_index shape := by
  unfold Shape.max_index
  rw [List.toNats_cons, Nat.prod_cons]

def Shape.max_index_posint (shape : Shape) : PosInt :=
  ⟨ shape.max_index, by
    unfold Shape.max_index
    simp [Shape.max_index, Nat.prod]
    induction shape
    case nil =>
      rw [List.toNats_nil, List.foldr_nil]
      simp
    case cons hd tl ih =>
      rw [List.toNats_cons, List.foldr_cons]
      simp_all only [Nat.mul_pos_iff_of_pos_right]
      exact hd.property
  ⟩

theorem Shape.max_index_posint_coe (shape : Shape) :
  (Shape.max_index_posint shape : Nat) = Shape.max_index shape := by
  unfold Shape.max_index_posint Shape.max_index
  simp

def Stride.from_shape_cons_max_index (hd : PosInt) (tl : List PosInt) :
  Stride.from_shape (hd :: tl) =
  Shape.max_index_posint tl :: Stride.from_shape tl := by
  rw [Stride.from_shape_cons]
  simp
  congr
  unfold Shape.max_index_posint Shape.max_index
  induction tl
  case nil =>
    simp
    rw [Stride.from_shape_nil]
    simp
    conv in [].toNats => rw [List.toNats_nil]
    conv in Nat.prod [] => rw [Nat.prod_nil]
    -- this is annoying: everytime I'm multiplying PosInts, I can't just use omega...
    simp [instHMulPosInt]
  case cons hd' tl' ih =>
    rw [Stride.from_shape_cons]
    unfold List.head?
    simp
    rw [ih]
    conv =>
      rhs
      enter [1]
      rw [List.toNats_cons, Nat.prod_cons]
    simp [instHMulPosInt]

/--
Returns whether an index is valid for a given shape by checking:
1. The index length matches the shape length
2. Each index component is less than the corresponding shape dimension
-/
def Shape.is_valid_index (s : Shape) (idx : List Nat) : Prop :=
  ∃ (hlen: idx.length = s.length),
  ∀ (i : Nat) (h : i < idx.length),
    idx.get ⟨i, h⟩ < s.get ⟨i, by rw [hlen] at h; exact h⟩

/--
The type of valid indices for a given shape
-/
def IndexSet (s : Shape) : Type :=
  {idx : List Nat // Shape.is_valid_index s idx}

def IndexSet.zero (shape : Shape) : IndexSet shape :=
  ⟨ (List.map (fun x => 0) shape), by
      unfold Shape.is_valid_index
      simp
      intros i hi_bound
      exact (shape.get ⟨i, hi_bound⟩).property
  ⟩

-- Can't I do something like this?
-- theorem List.head!_eq_getElem_zero (l : List α) [Inhabited α] (h: 0 < l.length) : l.head! = l.get ⟨0, h⟩ := by


@[simps! apply symm_apply]
def IndexSet.from_single_dimension_equiv {shape : PosInt} :
  IndexSet [shape] ≃ NatLt shape where
  toFun := Subtype.map
    (fun x => x.headD 0)
    (by
      intro x hvalid
      unfold Shape.is_valid_index at hvalid
      obtain ⟨hlen, hvalid⟩ := hvalid
      have := hvalid 0 (by rw [hlen]; simp)
      have hx_nonempty : x ≠ [] := by
        simp at hlen
        apply List.ne_nil_of_length_pos
        rw [hlen]
        simp
      simp at this
      simp
      rw [List.getElem_zero] at this
      have := List.head?_eq_head hx_nonempty
      rw [this]
      simp
      assumption
    )
  invFun := Subtype.map (fun x => [x]) (by sorry)
  left_inv := by sorry
  right_inv := by sorry

@[simps! apply symm_apply]
def IndexSet.cons_equiv {shapeHead : PosInt} {shapeTail : Shape} :
  IndexSet (shapeHead :: shapeTail) ≃ IndexSet [shapeHead] × IndexSet shapeTail
  where
  /- TODO: define this with Subtype.map as well? -/
  toFun := (Prod.map
              (Subtype.map (fun idx => [idx.headD 0]) (by sorry))
              (Subtype.map (fun idx => idx.tail) (by sorry)))
              ∘ (fun x => (x, x))
  invFun :=
     fun (idxHead, idxTail) => ⟨idxHead.val.head (by sorry) :: idxTail.val, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

def IndexSet.cons_embed {shapeHead : PosInt} {shapeTail : Shape} :
  IndexSet [shapeHead] → IndexSet (shapeHead :: shapeTail) :=
  Subtype.map (fun idx => idx.headD 0 :: (IndexSet.zero shapeTail).val) (by sorry)

def IndexSet.cons_embed_tail {shapeHead : PosInt} {shapeTail : Shape} :
  IndexSet shapeTail → IndexSet (shapeHead :: shapeTail) :=
  Subtype.map (fun idx => 0 :: idx) (by sorry)

/- Not sure if this is going to be useful without proving many additional theorems
theorem IndexSet.cons_embed_sum {shapeHead : PosInt} {shapeTail : Shape} :
  (IndexSet.cons_equiv.symm : IndexSet [shapeHead] × IndexSet shapeTail → IndexSet (shapeHead :: shapeTail))
  = (IndexSet.cons_embed ∘ Prod.fst) + (IndexSet.cons_embed_tail ∘ Prod.snd) := by
  simp
-/


theorem Shape.max_index_tail : ∀ (s : Shape) (s' : PosInt),
  Shape.max_index (s' :: s) = s' * Shape.max_index s := by
  intro s s'
  unfold Shape.max_index
  unfold Nat.prod
  unfold List.toNats
  simp

theorem Shape.max_index_tail_increase : ∀ (s : Shape) (s' : PosInt),
  Shape.max_index (s' :: s) ≥ Shape.max_index s := by
  intro s s'
  rewrite [Shape.max_index_tail]
  have h : (s' : Nat) > 0 := by
    exact s'.property
  exact Nat.le_mul_of_pos_left s.max_index h


/- ## IndexSet as functions: experimental -/


def IndexFnSet (s : Shape) : Type :=
  { f : Fin s.length → Nat // ∀ i, f i < s.get ⟨i, by simp⟩ }


@[simps! apply symm_apply]
def IndexSet.fn_equiv {shape : Shape} :
  IndexSet shape ≃ IndexFnSet shape :=
  { toFun x := ⟨fun i => x.val[i]' (by
      -- have h_idx := x.property
      -- unfold Shape.is_valid_index at h_idx
      obtain ⟨hlen, h_idx⟩ := x.property
      rw [hlen]
      exact i.is_lt
      ),
      by
      obtain ⟨hlen, h_idx⟩ := x.property
      intro i
      apply h_idx
    ⟩,
    invFun f := ⟨List.ofFn f.val, by
      unfold Shape.is_valid_index
      have : (List.ofFn f.val).length = List.length shape := by simp
      exists this
      intro i hi

      rw [List.get_ofFn]
      apply f.property
     ⟩
    left_inv := by sorry,
    right_inv := by sorry }

def incrementIndex {s : Shape} (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j) : IndexFnSet s :=
  ⟨fun k => if k = j then i.val k + 1 else i.val k, by
    intro k
    by_cases hkj : k = j
    · rw [hkj]; simp; exact h
    · simp; rw [if_neg hkj]; exact i.property k⟩
