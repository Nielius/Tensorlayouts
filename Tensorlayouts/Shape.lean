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
def Stride := List Nat -- allowing 0 for stride might even be easier

deriving instance Repr for Shape
deriving instance Repr for Stride
deriving instance DecidableEq for Shape
deriving instance DecidableEq for Stride
deriving instance Append for Shape
deriving instance Append for Stride

instance : Coe (List PosInt) (List Nat) :=
  ⟨List.map Subtype.val⟩

instance : Coe Shape (List Nat) :=
  ⟨List.map Subtype.val⟩

instance : GetElem (List PosInt) Nat PosInt (fun s i => i < s.length) where
  getElem s i h := s.get ⟨i, h⟩

-- def List.toNats (l : List PosInt) : List Nat :=
--   List.map (fun (x: PosInt) => (x : Nat)) l

-- theorem List.toNats_length (l : List PosInt) : List.length (List.toNats l) = List.length l := by
--   unfold List.toNats
--   simp

-- theorem List.toNats_getElem (l : List PosInt) (i : Nat) (h : i < List.length l) :
--   (List.toNats l).get ⟨i, (List.toNats_length l) ▸ h⟩ = l.get ⟨i, h⟩ := by
--   unfold List.toNats
--   simp

-- theorem List.toNats_nil : List.toNats [] = [] := by
--   unfold List.toNats
--   simp

-- theorem List.toNats_cons (hd : PosInt) (tl : List PosInt)  :
--   List.toNats (hd :: tl) = (hd : Nat) :: List.toNats tl := by
--   unfold List.toNats
--   simp

/- These don't seem to be necessary, because you can just use simp?
   Or maybe List.map_cons?
theorem ListPosInt.toNats_cons (hd : PosInt) (tl : List PosInt) :
  ((hd :: tl) : List Nat) = (hd : Nat) :: (tl : List Nat) := by
  simp?

theorem Shape.coe_cons (hd : PosInt) (tl : Shape) :
  ((hd :: tl) : List Nat) = (hd : Nat) :: (tl : List Nat) := by
  simp
-/

def Stride.from_shape (shape : Shape) : Stride :=
  List.tail (List.scanr (· * ·) 1 shape)

theorem Stride.from_shape_nil : Stride.from_shape [] = [] := by unfold Stride.from_shape; simp

theorem Stride.from_shape_cons (hd : PosInt) (tl : List PosInt) :
  Stride.from_shape (hd :: tl) =
    let stride_tail := Stride.from_shape tl
    (tl.headD ⟨1, by simp⟩ * stride_tail.headD 1) :: stride_tail := by
  unfold Stride.from_shape
  simp

  induction tl
  case nil =>
    simp
  case cons hd' tl' ih =>
    simp
    congr
    rw [List.getElem?_zero_getD_eq_headD]
    rw [List.scanr_headD_eq_foldr]

theorem Stride.from_shape_length (shape : Shape) : List.length (Stride.from_shape shape) = List.length shape :=
  by simp only [Stride.from_shape,List.scanr_length_tail, List.length_map]



/- ## Indexing for shapes -/

/--
 Strict upper bound for the index that the shape can represent
 in the shape's canonical view.
 'Strict' means strict inequality, i.e. idx < shape.max_index
-/
def Shape.max_index (shape : Shape) : Nat :=
  Nat.prod shape

theorem Shape.max_index_cons (a : PosInt) (shape : Shape) :
  Shape.max_index (a :: shape) = a * Shape.max_index shape := by
  simp only [Shape.max_index, List.map_cons, Nat.prod_cons]

def Shape.max_index_posint (shape : Shape) : PosInt :=
  ⟨ shape.max_index, by
    unfold Shape.max_index
    simp [Shape.max_index, Nat.prod]
    induction shape
    case nil =>
      simp only [List.map_nil, List.foldr_nil, Nat.lt_add_one]
    case cons hd tl ih =>
      rw [List.map_cons, List.foldr_cons]
      simp_all only [Nat.mul_pos_iff_of_pos_right]
      exact hd.property
  ⟩

@[simp]
theorem Shape.max_index_posint_coe (shape : Shape) :
  (Shape.max_index_posint shape : Nat) = Shape.max_index shape :=
  by
   simp only [Shape.max_index_posint, Shape.max_index]

def Stride.from_shape_cons_eq_max_index (hd : PosInt) (tl : Shape) :
  Stride.from_shape (hd :: tl) =
  (Shape.max_index_posint tl : Nat) :: Stride.from_shape tl := by
  rw [Stride.from_shape_cons]
  simp
  congr
  unfold Shape.max_index
  induction tl
  case nil =>
    simp only [List.head?_nil, Option.getD_none, Nat.one_mul, List.map_nil, Stride.from_shape_nil]
    rfl
  case cons hd' tl' ih =>
    rw [Stride.from_shape_cons]
    unfold List.head?
    simp [ih, Nat.prod_cons]


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

@[simp]
theorem IndexSet.zero_length (shape : Shape) : (IndexSet.zero shape).val.length = shape.length := by
  unfold IndexSet.zero
  simp only [List.map_const', List.length_replicate]

@[simp]
theorem IndexSet.zero_getElem_zero {shape : Shape } :
  ∀ (i : Fin shape.length), (IndexSet.zero shape).val[i] = 0 := by
  unfold IndexSet.zero
  simp

@[simp]
theorem IndexSet.zero_getElem_zero' {shape : Shape } (i : Nat) (hi : i < shape.length) :
  (IndexSet.zero shape).val[i]' (by simp; exact hi) = 0 := by
  unfold IndexSet.zero
  simp

@[simp]
theorem IndexSet.val_length {s : Shape} (i : IndexSet s) : i.val.length = s.length := by
  have := i.property
  unfold Shape.is_valid_index at this
  obtain ⟨hlen, hvalid⟩ := this
  exact hlen

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
  invFun := Subtype.map (fun x => [x]) (by unfold Shape.is_valid_index; simp)
  left_inv := by
    unfold Function.LeftInverse
    intro x
    rw [Subtype.map_comp]
    unfold Function.comp
    unfold Subtype.map
    apply Subtype.ext
    simp
    have h_len : x.val.length = 1 := by simp only [val_length, List.length_singleton]
    rw [List.eq_cons_of_length_one h_len]
    simp
  right_inv := by
    unfold Function.RightInverse
    intro x
    rw [Subtype.map_comp]
    unfold Function.comp
    unfold Subtype.map
    simp



def IndexSet.cons_embed {shapeHead : PosInt} {shapeTail : Shape} :
  IndexSet [shapeHead] → IndexSet (shapeHead :: shapeTail) :=
  Subtype.map (fun idx => idx.headD 0 :: (IndexSet.zero shapeTail).val) (by
    intro a a_valid
    unfold Shape.is_valid_index
    obtain ⟨hlen, hvalid⟩ := a_valid
    simp
    intro i hi
    cases i  with
    | zero =>
      have := hvalid 0 (by simp at hlen; simp [hlen])
      cases a with
      | nil =>
        simp at hlen
      | cons a_head a_tail =>
        simp
        simp at this
        exact this
    | succ i' =>
      simp
      rw [IndexSet.zero_getElem_zero' i']
      exact (shapeTail.get ⟨i', by simp at hlen; apply Nat.lt_of_succ_lt_succ; assumption ⟩).property
      apply Nat.lt_of_succ_lt_succ; assumption
  )


def IndexSet.cons_embed_tail {shapeHead : PosInt} {shapeTail : Shape} :
  IndexSet shapeTail → IndexSet (shapeHead :: shapeTail) :=
  Subtype.map (fun idx => 0 :: idx) (by
    intro a a_valid
    unfold Shape.is_valid_index
    obtain ⟨hlen, hvalid⟩ := a_valid
    simp

    exists hlen

    intro i hi
    cases i with
    | zero =>
      simp
      exact shapeHead.property
    | succ i' =>
      have hi' : i' < a.length := by apply Nat.lt_of_succ_lt_succ ; exact hi
      exact hvalid i' hi'
  )

/- Not sure if this is going to be useful without proving many additional theorems
theorem IndexSet.cons_embed_sum {shapeHead : PosInt} {shapeTail : Shape} :
  (IndexSet.cons_equiv.symm : IndexSet [shapeHead] × IndexSet shapeTail → IndexSet (shapeHead :: shapeTail))
  = (IndexSet.cons_embed ∘ Prod.fst) + (IndexSet.cons_embed_tail ∘ Prod.snd) := by
  simp
-/


def IndexSet.incrementNth {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j) : IndexSet s :=
  ⟨ i.val.incrementNth j, by
    unfold Shape.is_valid_index

    exists ?_
    . simp
    . intro k h_k_len
      simp at h_k_len
      have := i.val.incrementNth_ite j ⟨ k, by rw [IndexSet.val_length]; exact h_k_len ⟩
      simp at this

      by_cases h_k_eq_j : k = j
      . rw [if_pos h_k_eq_j] at this
        simp
        rw [this]
        subst h_k_eq_j
        assumption
      . rw [if_neg h_k_eq_j] at this
        simp
        rw [this]
        obtain ⟨hlen, hvalid⟩ := i.property
        refine hvalid k _
  ⟩

@[simp]
theorem IndexSet.incrementNth_val_length {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j) :
  (i.incrementNth j h).val.length = s.length := by
  unfold IndexSet.incrementNth
  simp

theorem IndexSet.incrementNth_val_length_eq {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j) :
  (i.incrementNth j h).val.length = i.val.length := by
  unfold IndexSet.incrementNth
  simp only [List.incrementNth_length, val_length]

@[simp]
theorem IndexSet.incrementNth_val_eq {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j) :
  (i.incrementNth j h).val = i.val.incrementNth j := by
  unfold IndexSet.incrementNth
  simp only [List.incrementNth_length, val_length]

theorem IndexSet.incrementNth_ite_val_switched {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j)
  (k : Fin (i.incrementNth j h).val.length)
  : (i.incrementNth j h).val.get k =
       if k.val = j.val then i.val.get (Fin.cast (by apply i.incrementNth_val_length_eq) k) + 1 else i.val.get (Fin.cast (by apply i.incrementNth_val_length_eq) k) := by
  unfold IndexSet.incrementNth
  simp
  have := (i.val).incrementNth_ite (j.val) (Fin.cast (by apply i.incrementNth_val_length_eq) k)
  unfold Fin.cast at this
  simp at this
  rw [this]

theorem IndexSet.incrementNth_ite {s : Shape} (i : IndexSet s) (j : Fin s.length) (h : i.val[j] + 1 < s.get j)
  (k : Fin (i.incrementNth j h).val.length)
  : (i.val.incrementNth j).get k =
       if k.val = j.val then i.val.get (Fin.cast (by apply i.incrementNth_val_length_eq) k) + 1 else i.val.get (Fin.cast (by apply i.incrementNth_val_length_eq) k) := by
  unfold IndexSet.incrementNth
  simp
  have := (i.val).incrementNth_ite (j.val) (Fin.cast (by apply i.incrementNth_val_length_eq) k)
  unfold Fin.cast at this
  simp at this
  rw [this]

def IndexSet.one_hot {s : Shape}  (j : Fin s.length) (h : 1 < (s.get j).val) : IndexSet s :=
  IndexSet.incrementNth (IndexSet.zero s) j (by simp; exact h)

theorem IndexSet.one_hot_val {s : Shape} (j : Fin s.length) (h : 1 < (s.get j).val) :
  (IndexSet.one_hot j h).val = List.one_hot s.length j := by
  unfold IndexSet.one_hot
  unfold IndexSet.incrementNth
  simp
  apply List.ext_get
  simp

  intro i hi hi2
  rw [IndexSet.incrementNth_ite]
  unfold List.one_hot
  have := List.incrementNth_ite (List.zeros s.length) j ⟨ i, by simp; simp at hi2; exact hi2 ⟩
  simp
  simp at this
  rw [this]
  unfold List.zeros
  simp

  simp [IndexSet.zero, List.one_hot, List.zeros]
  simp
  assumption


theorem Shape.max_index_tail : ∀ (s : Shape) (s' : PosInt),
  Shape.max_index (s' :: s) = s' * Shape.max_index s := by
  intro s s'
  unfold Shape.max_index
  unfold Nat.prod
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


-- @[simps! apply symm_apply]
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
    left_inv := by
      unfold Function.LeftInverse
      intro x
      simp
      apply Subtype.ext
      simp
      have h_almost := List.ofFn_getElem (l := x.val)
      have hlen : x.val.length = shape.length := by simp

      have := Eq.rec (motive := fun ln (hln: x.val.length = ln)  => (@List.ofFn ℕ x.val.length fun (i : Fin x.val.length) ↦ x.val[i.val]) = (@List.ofFn ℕ ln fun i ↦ x.val.get (Fin.cast hln.symm i)))
        (by rfl) hlen
      unfold Fin.cast at this
      rw [this] at h_almost
      exact h_almost,
    right_inv := by
      unfold Function.RightInverse
      unfold Function.LeftInverse
      intro x
      simp
    }

theorem IndexSet.fn_equiv_symm_val_length {s : Shape} {i : IndexFnSet s} : (IndexSet.fn_equiv.symm i).val.length = s.length := by
  unfold IndexSet.fn_equiv
  simp

theorem IndexSet.fn_equiv_symm_val_getElem {s : Shape} {i : IndexFnSet s} {j : Fin s.length} :
  (IndexSet.fn_equiv.symm i).val[j] = i.val j := by
  unfold IndexSet.fn_equiv
  simp

-- I could define this for lists as well; see IndexSet.fn_equiv_symm_of_increment; might make some proofs easier
def incrementIndex {s : Shape} (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j) : IndexFnSet s :=
  ⟨fun k => if k.val = j.val then i.val k + 1 else i.val k, by
    intro k
    by_cases hkj : k = j
    · rw [hkj]; simp; exact h
    · simp
      have hneq : k.val ≠ j.val := by
        have := Fin.eq_of_val_eq.mt hkj
        unfold Ne
        assumption
      rw [if_neg hneq]; exact i.property k⟩

theorem incrementIndex_fn_equiv {s : Shape} (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j) :
  IndexSet.fn_equiv.symm (incrementIndex i j h) = (IndexSet.fn_equiv.symm i).incrementNth j (by
    rw [IndexSet.fn_equiv_symm_val_getElem]; assumption
  ) := by
  /-
  This theorem states that the following diagram commutes:

       IndexFnSet   --- incrementIndex ---> IndexFnSet
           |                                    |
           | fn_equiv                           | fn_equiv
           v                                    v
       IndexSet     --- incrementNth --->   IndexSet
  -/

  unfold incrementIndex
  apply Subtype.ext
  simp
  apply List.ext_get
  . simp -- proves lengths are equal
  . intro n hn hn2
    rw [IndexSet.incrementNth_ite (IndexSet.fn_equiv.symm i) j]
    simp [IndexSet.fn_equiv]
    rw [IndexSet.fn_equiv_symm_val_getElem]
    assumption


def IndexFnSet.zero (s : Shape) : IndexFnSet s :=
  ⟨fun _ => 0, by
    intro i
    simp
    exact (s.get i).property
 ⟩

@[simp]
theorem IndexFnSet.zero_equiv {s : Shape} : IndexSet.fn_equiv (IndexSet.zero s) = IndexFnSet.zero s := by
  simp [IndexSet.fn_equiv]
  unfold IndexFnSet.zero
  apply Subtype.ext
  simp

@[simp]
theorem IndexFnSet.zero_val_zero {s : Shape} : (IndexFnSet.zero s).val = fun _ => 0 := by unfold IndexFnSet.zero; rfl


theorem IndexFnSet.cases {s : Shape} (i : IndexFnSet s) :
    i = IndexFnSet.zero s
  ∨ ∃ (j : Fin s.length) (i' : IndexFnSet s) (h : i'.val j + 1 < s.get j),
    i = incrementIndex i' j h
  := by
  by_cases h : ∀ j : Fin s.length, i.val j = 0

  · left -- all elements in i are 0
    have hi0 : i = IndexFnSet.zero s := by
      apply Subtype.ext
      funext j
      rw [h]
      simp

    subst hi0
    rfl

  · right -- some element is not 0
    have h_not_0 : ∃ j : Fin s.length, i.val j ≠ 0 := by
      rw [<- not_forall]
      exact h
    obtain ⟨j, hj⟩ := h_not_0

    cases h : i.val j with
    | zero =>
      contradiction
    | succ i_j =>

      let i' : IndexFnSet s := ⟨
        fun k => if k.val = j.val then i_j else i.val k,
        by
        intro k
        by_cases hkj : k = j
        · rw [hkj]; simp
          apply (Nat.lt_trans (m := i_j + 1))
          . simp
          . have := i.property j
            rw [h] at this
            exact this
        . simp
          rw [if_neg (Fin.eq_of_val_eq.mt hkj)]
          exact i.property k
      ⟩

      exists j, i'

      have h_i' : i'.val j + 1 < s.get j := by
        unfold i'
        simp
        rw [<- h]
        exact i.property j
      exists h_i'

      -- Now to prove that they are equal
      apply Subtype.ext
      funext k
      by_cases hkj : k = j
      · rw [hkj]
        unfold i'
        unfold incrementIndex
        simp
        assumption
      · unfold i'
        unfold incrementIndex
        simp
        repeat rw [if_neg (Fin.eq_of_val_eq.mt hkj)]


-- To do the induction, we're introducing a new property: the sum of all the integers in the index
def IndexFnSet.sum (i : IndexFnSet s) : Nat :=
  ∑ j : Fin s.length, i.val j
  -- Finset.sum (Finset.univ : Finset (Fin s.length)) (fun j => i.val j)
  -- ∑ j in (Fin s.length).as_range, i.val j
  -- List.sum (List.ofFn i.val)

theorem split_sum (n : Nat) (j : Fin n) (f : Fin n → Nat) :
  (∑ i : Fin n, f i) = (∑ i in Finset.univ.filter (fun i => i ≠ j), f i) + f j :=
  by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i = j) f]
  conv =>
    lhs
    simp [Finset.filter_eq', Finset.sum_singleton]
    rw [Nat.add_comm]


theorem IndexFnSet.sum_zero {s : Shape} : IndexFnSet.sum (IndexFnSet.zero s) = 0 := by
  simp [IndexFnSet.sum]

theorem IndexFnSet.sum_increment {s : Shape} (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j) :
  IndexFnSet.sum (incrementIndex i j h) = IndexFnSet.sum i + 1 := by
  unfold IndexFnSet.sum
  repeat rw [split_sum (s.length) j]
  unfold incrementIndex
  simp
  rw [Nat.add_assoc]
  apply congrArg (· + (i.val j + 1))
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx  -- Simplify the filter condition
  have h : x ≠ j := hx  -- From the filter, x ≠ j
  have h_val : x.val ≠ j.val := by  -- Prove ↑x ≠ ↑j
    intro contra
    rw [<- Fin.ext_iff] at contra
    contradiction
  rw [if_neg h_val]  -- Since ↑x ≠ ↑j, the if condition is false, so use the else branch


theorem IndexFnSet.sum_eq_zero_implies_zero {s : Shape} (i :  IndexFnSet s) : IndexFnSet.sum i = 0 → i = IndexFnSet.zero s := by
  -- can prove this with the cases theorem
  obtain h_zero | ⟨j, i', h, h_step⟩ := IndexFnSet.cases i
  . rw [h_zero]
    simp
  . rw [h_step]
    intro h_sum_zero
    rw [IndexFnSet.sum_increment] at h_sum_zero
    contradiction


theorem IndexFnSet._induction_helper {s : Shape} (P : IndexFnSet s → Prop)
  (h0 : P (IndexSet.fn_equiv (IndexSet.zero s)))
  (step : ∀ (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j), P i → P (incrementIndex i j h)) :
  ∀ (n : Nat) (i : IndexFnSet s) (_ : i.sum = n), P i := by
  intro n
  induction n with
  | zero =>
    intro i h_i_sum_zero
    have h_i_is_0 : i = IndexFnSet.zero s := by
      apply IndexFnSet.sum_eq_zero_implies_zero
      exact h_i_sum_zero
    simp at h0
    subst h_i_is_0
    assumption
  | succ n ih =>
    intro i h_i_sum_succ

    have := IndexFnSet.cases i
    cases this with
    | inl h_i_is_0 =>
      rw [h_i_is_0]
      simp at h0
      subst h_i_is_0
      assumption
    | inr h1 =>
      rcases h1 with ⟨j, i', h, h_step⟩
      rw [h_step]
      apply step
      apply ih
      have h_i_sum_n : i.sum = i'.sum + 1 := by
        rw [<- IndexFnSet.sum_increment i' j h]
        rw [h_step]
      rw [h_i_sum_n] at h_i_sum_succ
      simp at h_i_sum_succ
      assumption


theorem IndexFnSet.induction {s : Shape} (P : IndexFnSet s → Prop)
  (h0 : P (IndexSet.fn_equiv (IndexSet.zero s)))
  (step : ∀ (i : IndexFnSet s) (j : Fin s.length) (h : i.val j + 1 < s.get j), P i → P (incrementIndex i j h)) :
  ∀ (i : IndexFnSet s), P i :=
  fun i => IndexFnSet._induction_helper P h0 step i.sum i (by rfl)


theorem IndexSet.fn_equiv_symm_of_increment {s : Shape}
  (i : IndexFnSet s)
  (j : Fin s.length)
  (h : i.val j + 1 < (s.get j).val)
  (k : Fin s.length)
  : (IndexSet.fn_equiv.symm (incrementIndex i j h)).val.get (Fin.cast IndexSet.fn_equiv_symm_val_length.symm k)
    = (if k.val = j.val then i.val k + 1 else i.val k) := by
  unfold IndexSet.fn_equiv
  unfold incrementIndex
  simp


theorem IndexSet.fn_equiv_symm_of_increment' {s : Shape}
  (i : IndexFnSet s)
  (j : Fin s.length)
  (h : i.val j + 1 < (s.get j).val)
  (k : Fin (IndexSet.fn_equiv.symm (incrementIndex i j h)).val.length)
  : (IndexSet.fn_equiv.symm (incrementIndex i j h)).val.get k
    = (if k.val = j.val then i.val (Fin.cast IndexSet.fn_equiv_symm_val_length k) + 1 else i.val (Fin.cast IndexSet.fn_equiv_symm_val_length k)) := by
    -- = (if k.val = j.val then i.val ⟨ k.val, by  ⟩ + 1 else i.val ⟨ k.val, by sorry ⟩) := by
  unfold IndexSet.fn_equiv
  unfold incrementIndex
  unfold Fin.cast
  simp
