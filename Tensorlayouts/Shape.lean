import Aesop
import Tensorlayouts.ArithHelpers
import Tensorlayouts.CastingLemmas
import Tensorlayouts.LinearIntegerFunc
import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp
import Mathlib.Data.List.Zip -- needed for List.zipWith_map_right
import Mathlib.Logic.Equiv.Basic

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
 Upper bound for the index that the shape can represent
 in the shape's canonical view.
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


@[simps! apply symm_apply]
def IndexSet.from_single_dimension_equiv {shape : PosInt} :
  IndexSet [shape] ≃ NatLt shape where
  toFun x := ⟨x.val.head (fun hempty => by
    have h : _ := x.property
    unfold Shape.is_valid_index at h
    obtain ⟨hlen, hvalid⟩ := h
    simp at hlen
    rw [hempty] at hlen
    simp at hlen
    ), by
        have h : _ := x.property
        unfold Shape.is_valid_index at h
        obtain ⟨hlen, hvalid⟩ := h
        have hvalid' := hvalid 0 (by rw [hlen]; simp)
        simp at hvalid'
        rw [List.head_eq_getElem_zero]
        assumption
     ⟩
  invFun x := ⟨[x.val], by sorry⟩
  left_inv := by sorry
  right_inv := by sorry


/--
s : Shape
n : ℕ
hbound : n < s.max_index
shape_eq : (View.from_shape s).shape = s
stride_eq : (View.from_shape s).stride = Stride.from_shape s
strides : Stride := Stride.from_shape s
strides_eq : strides = Stride.from_shape s
⊢ (List.zipWith (fun a b ↦ a * (n / a % b)) (List.toNats strides) (List.toNats s)).sum = n
-/

theorem max_index_tail : ∀ (s : Shape) (s' : PosInt),
  Shape.max_index (s' :: s) = s' * Shape.max_index s := by
  intro s s'
  unfold Shape.max_index
  unfold Nat.prod
  unfold List.toNats
  simp

theorem max_index_tail_increase : ∀ (s : Shape) (s' : PosInt),
  Shape.max_index (s' :: s) ≥ Shape.max_index s := by
  intro s s'
  rewrite [max_index_tail]
  have h : (s' : Nat) > 0 := by
    exact s'.property
  exact Nat.le_mul_of_pos_left s.max_index h

/- ## Heterogenous base -/

namespace HeterogenousBase

/-- back-and-forth in the heterogeneous base; mostly a helper function -/
def heterogenous_base_bnf (s : Shape) : Nat -> Nat :=
  fun x =>
    (Stride.from_shape s).toNats.inner_prod
    (List.zipWith (fun shape stride => (x / stride % shape)) s.toNats (Stride.from_shape s).toNats)


theorem heterogenous_base_bnf_cons : ∀ (shead : PosInt) (stail : Shape) (x : Nat),
  heterogenous_base_bnf (shead :: stail) x =
  (Shape.max_index_posint stail * (x / Shape.max_index_posint stail % shead)) +
  heterogenous_base_bnf stail x := by
  intro shead stail x
  unfold heterogenous_base_bnf
  rw [Stride.from_shape_cons_max_index]
  rw [List.toNats_cons]
  rw [List.toNats_cons]
  rw [List.zipWith_cons_cons]
  rw [List.inner_prod_cons]


/--
A representation of a number in a heterogeneous base consisting of two digits,
including the overflow to what would be the next digit.

This structure is convenient for the proof of the correctness of the heterogenous base,
because it has just enough information to do the induction step.

The idea is: p: PairBaseRepresentation = {size2, size1, n}
represents the number n written in a base (size2, size1), with
any overflow going to p.overflow.

See also https://en.wikipedia.org/wiki/Mixed_radix

The relevance to tensor layouts is that the unravel function for
a shape s is equal to the function that sends a number to
its representation in the mixed radix base given by the shape s.
-/
structure PairBaseRepresentation where
  size2: PosInt -- radix 2
  size1: PosInt -- radix 1
  n: Nat
  deriving Repr, DecidableEq

section PairBaseRepresentationProperties
variable (p : PairBaseRepresentation)

def PairBaseRepresentation.overflow : Nat :=
  p.n % (p.size2 * p.size1)

def PairBaseRepresentation.digit2 : Nat :=
  (p.n / p.size1) % p.size2

def PairBaseRepresentation.digit1 : Nat :=
  p.n % p.size1

theorem PairBaseRepresentation.digit2_lt_size : p.digit2 < p.size2 := by
  unfold PairBaseRepresentation.digit2
  apply Nat.mod_lt
  exact p.size2.property

theorem PairBaseRepresentation.digit1_lt_size : p.digit1 < p.size1 := by
  unfold PairBaseRepresentation.digit1
  apply Nat.mod_lt
  exact p.size1.property
end PairBaseRepresentationProperties

section PairBaseRepresentationTheorems

variable (p : PairBaseRepresentation)
theorem PairBaseRepresentation.first_digits_size : p.size1 * p.digit2 + p.digit1 = p.n % (p.size2 * p.size1) := by
  unfold PairBaseRepresentation.digit2 PairBaseRepresentation.digit1

  have hdigit2 : (p.n / ↑p.size1 % ↑p.size2) = (p.n % (↑p.size2 * ↑p.size1)) / ↑p.size1 := by
    calc
      (p.n / ↑p.size1 % ↑p.size2)
        = (p.n % (↑p.size1 * ↑p.size2) / ↑p.size1) := ?_
      _ = (p.n % (↑p.size2 * ↑p.size1) / ↑p.size1) := ?_
    . rw [Nat.mod_mul_right_div_self]
    . rw [Nat.mul_comm]

  have hdigit1 : (p.n % ↑p.size1) = (p.n % (↑p.size2 * ↑p.size1)) % ↑p.size1 := by
    calc
      (p.n % ↑p.size1)
        = (p.n % (↑p.size2 * ↑p.size1)) % ↑p.size1 := ?_
      _ = (p.n % (↑p.size2 * ↑p.size1)) % ↑p.size1 := ?_
    . rw [Nat.mod_mul_left_mod]
    . rw [Nat.mul_comm]

  rw [hdigit2, hdigit1]
  exact Nat.div_add_mod (p.n % (↑p.size2 * ↑p.size1)) ↑p.size1

-- set_option pp.parens true

-- theorem PairBaseRepresentation.from_nat_to_nat :
--   p.overflow + p.size1 * p.digit2 + p.digit1 = p.n := by
--   unfold PairBaseRepresentation.overflow PairBaseRepresentation.digit2 PairBaseRepresentation.digit1

--   sorry -- we don't really need this; but should not be so difficult to prove with the above proof

end PairBaseRepresentationTheorems

theorem heterogenous_base : ∀ (s : Shape) (x : Nat),
   heterogenous_base_bnf s x = x % s.max_index := by
  intro s
  induction s
  case nil =>
    intro x
    unfold heterogenous_base_bnf
    unfold Shape.max_index
    unfold Nat.prod
    unfold List.toNats
    unfold List.inner_prod
    simp
    omega

  case cons shape_head shape_tail tail_ih =>
    intro x

    let p : PairBaseRepresentation := {
      size2 := shape_head,
      size1 := Shape.max_index_posint shape_tail,
      n := x
    }

    rw [heterogenous_base_bnf_cons]
    rw [tail_ih]

    have hsize2: p.size2 = shape_head := by rfl
    rw [← hsize2]

    have hsize1: p.size1 = Shape.max_index_posint shape_tail := by rfl
    rw [← hsize1]

    have hsize1': p.size1 = Shape.max_index shape_tail := by rfl
    rw [← hsize1']

    have hmaxsize : p.size2 * p.size1 =  Shape.max_index (shape_head :: shape_tail) := by rfl
    rw [← hmaxsize]

    have hx : p.n = x := by rfl
    rw [← hx]
    apply (PairBaseRepresentation.first_digits_size p)

end HeterogenousBase

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

theorem View.from_shape_nil : View.from_shape [] = {shape := [], stride := [], lengthEq := by simp} := by
  simp [View.from_shape, Stride.from_shape]

theorem View.from_shape_shape_eq (s: Shape) : (View.from_shape s).shape = s := by
  unfold View.from_shape
  simp

theorem View.from_shape_stride_eq (s: Shape) : (View.from_shape s).stride = Stride.from_shape s := by
  unfold View.from_shape
  simp

theorem View.from_shape_stride_shape_length_eq (s: Shape) : (List.length s) = (View.from_shape s).stride.length := by
  unfold View.from_shape
  unfold Stride.from_shape
  rw [List.scanr_length_tail]

def View.from_single_dimension (shape stride : PosInt) : View := {
  shape := [shape],
  stride := [stride],
  lengthEq := by simp
}

theorem View.from_single_dimension_shape_eq (shape stride : PosInt) :
  (View.from_single_dimension shape stride).shape = [shape] := by
  unfold View.from_single_dimension
  simp

theorem View.from_single_dimension_stride_eq (shape stride : PosInt) :
  (View.from_single_dimension shape stride).stride = [stride] := by
  unfold View.from_single_dimension
  simp

theorem View.induction (P : View → Prop)
  (nil : P ⟨[], [], rfl⟩)
  (cons : ∀ (x : PosInt) (xs : Shape) (y : PosInt) (ys : Stride)
          (h : xs.length = ys.length)
          (ih : P ⟨xs, ys, h⟩),
          P ⟨x::xs, y::ys, congrArg Nat.succ h⟩) :
  ∀ (v : View), P v := by
  intro v
  cases v with
  | mk shape stride lengthEq =>
    -- Do induction on shape, but we need to handle stride in parallel
    revert stride
    induction shape with
    | nil =>
      -- In nil case, stride must also be nil due to length equality
      intros stride lengthEq
      have strideNil : stride = [] := by
        rw [List.length_nil] at lengthEq
        apply List.eq_nil_of_length_eq_zero
        exact Eq.symm lengthEq
      subst strideNil
      exact nil

    | cons head tail ih =>
      -- In cons case, stride must be non-empty due to length equality
      intros stride lengthEq
      cases stride with
      | nil =>
        rw [List.length] at lengthEq
        simp at lengthEq
      | cons y ys =>
        -- Use the inductive hypothesis with the tails
        have tailLenEq : tail.length = ys.length := by
          rw [List.length_cons] at lengthEq
          rw [List.length_cons] at lengthEq
          exact Nat.succ.inj lengthEq

        have ihP := ih ys tailLenEq
        exact cons head tail y ys tailLenEq ihP


/-- ### Index functions -/

def View.to_index_fn_unsafe (v : View) : List Nat → Option Nat
  | [] => if v.shape.length = 0 then some 0 else none
  | idx => if idx.length = v.shape.length then
            let pairs := List.zip idx v.stride.toNats
            some (List.foldr (fun (p : Nat × Nat) acc => p.1 * p.2 + acc) 0 pairs)
          else
            none

/--
  The smallest upper bound for the index that the view can represent.

  This is equal to ∑_i (s_i - 1) σ_i + 1, where σ_i is the ith stride, and s_i is the ith size.
  This assumes all strides are positive! In theory you could have negative strides...
-/
def View.max_index (v : View) : Nat :=
  v.stride.toNats.inner_prod (v.shape.toNats.map (fun x => x - 1)) + 1

theorem View.max_index_cons :
  ({ shape := shape_head :: shape_tail, stride := stride_head :: stride_tail, lengthEq := by sorry } : View).max_index
  = (shape_head - 1) * stride_head + ({ shape := shape_tail, stride := stride_tail, lengthEq := by sorry } : View).max_index := by
  unfold View.max_index
  simp [List.toNats_cons, List.inner_prod_cons, List.map_cons, List.foldr_cons]
  simp_arith
  apply Nat.mul_comm


theorem View.max_index_from_shape (s : Shape) : (View.from_shape s).max_index = s.max_index := by
  induction s
  case nil =>
    simp [View.max_index, Shape.max_index, List.toNats, Nat.prod, View.from_shape_nil]
    apply (@List.inner_prod_nil_nil Nat)

  case cons hd tl ih =>
    conv =>
      rhs
      rw [Shape.max_index_cons]

    conv =>
      lhs
      unfold View.from_shape
      pattern (Stride.from_shape (hd :: tl))
      rw [Stride.from_shape_cons_max_index]

    unfold View.max_index
    simp
    simp [List.toNats_cons, List.map_cons, List.inner_prod_cons]
    rw [← ih]

    have heq:  (List.toNats (Stride.from_shape tl)).inner_prod (List.map (fun x ↦ x - 1) tl.toNats) + 1 = (from_shape tl).max_index := by
      unfold View.max_index
      rw [View.from_shape_shape_eq, View.from_shape_stride_eq]

    conv =>
      lhs
      rw [Nat.add_assoc]
      rw [heq]

    have hsuf :  ↑(Shape.max_index_posint tl) = (from_shape tl).max_index := by
      rw [Shape.max_index_posint_coe]
      rw [ih]

    rw [hsuf]
    rw [Nat.mul_comm]
    rw [← Nat.succ_mul]
    simp_arith

    rw [Nat.sub_add_cancel]
    apply hd.property


theorem View.from_single_dimension_max_index_eq : ∀ (shape stride : PosInt),
  (View.from_single_dimension shape stride).max_index = (shape - 1) * stride + 1 := by
  intro shape stride
  unfold View.from_single_dimension
  unfold View.max_index
  simp [List.inner_prod, List.toNats]
  apply Nat.mul_comm

theorem View.from_single_dimension_max_index_le : ∀ (shape stride : PosInt),
  (View.from_single_dimension shape stride).max_index ≤ shape * stride := by
  intro shape stride
  rw [View.from_single_dimension_max_index_eq]
  rw [Nat.mul_comm]

  have hstride_pos : 1 ≤ stride.val := stride.property
  have hshape_pos : 1 ≤ shape.val := shape.property
  calc
    (stride : Nat) * (shape - 1) + 1 ≤ stride * (shape - 1) + stride := by sorry
    _ = stride * (shape - 1 + 1) := by apply Nat.mul_add_one
    _ = stride * shape := by rw [Nat.sub_add_cancel hshape_pos]

  rw [Nat.mul_comm]


-- theorem View.from_single_dimension_index_set_eq : ∀ (shape stride : PosInt),
--   (View.from_single_dimension shape stride).to_index_fn_unsafe = (fun idx => (shape - 1) * stride + idx) := by



def View.to_index_fn_safe (v : View) : (IndexSet v.shape) -> NatLt v.max_index :=
  fun ⟨idx, idx_bds⟩ => ⟨v.stride.toNats.inner_prod idx, by

    have hasdf : forall (n : Nat), n = v.shape.length -> (v.stride.toNats.inner_prod idx < v.max_index) := by
      -- introducing this is the only way I know of doing induction on n, while keeping the right hypotheses in the goal
      intro n hn
      induction n
      . have hshape_empty: v.shape = [] := by
          apply List.eq_nil_of_length_eq_zero
          exact (Eq.symm hn)

        have hstride_empty: v.stride = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hlen : v.stride.length = 0 := by
            rw [<- v.lengthEq]
            exact (Eq.symm hn)
          assumption

        simp [hshape_empty, hstride_empty]
        simp [View.max_index, List.toNats, List.inner_prod, List.map, List.foldr]

      case succ n ih =>
        -- I should have made sure the induction hypothesis holds for any view, not just this v

        have hshape_cons : _ := List.exists_cons_of_length_eq_add_one (Eq.symm hn)
        obtain ⟨shape_hd, shape_tl, hshape_cons'⟩ := hshape_cons

        -- have hstride_len : _ := List.length_eq_add_one_of_cons hshape_cons'
        have hstride_cons : _ := List.exists_cons_of_length_eq_add_one (Eq.symm hn)
        obtain ⟨stride_hd, stride_tl, hstride_cons'⟩ := hstride_cons

        sorry --- it is achievable from this point

    apply (hasdf v.shape.length (Eq.refl v.shape.length))
 ⟩
  -- we could add here that the result is always less than the max index

example : View :=
  View.from_shape [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨54, by simp⟩]


theorem View.from_single_dimension_index_fn_safe_eq (shape stride : PosInt) :
  (View.from_single_dimension shape stride).to_index_fn_safe =
  (fun idx => ⟨ (IndexSet.from_single_dimension_equiv idx).val * stride, by sorry ⟩) := by
  funext idx

  match idx with
  | ⟨idx_val, idx_bds⟩ =>
    match idx_val with
    | [] => sorry -- some contradiction here
    | idx_val_head :: idx_val_tail =>
      have idx_val_tail_eq : idx_val_tail = [] := by
        sorry

      simp [View.to_index_fn_safe, List.toNats, List.inner_prod, List.map, List.zipWith]
      rw [Nat.mul_comm]


theorem View.from_single_dimension_index_fn_safe_linear (shape stride : PosInt) (hshape : shape.val > 1) :
  NatLt.embed_nat ∘ (View.from_single_dimension shape stride).to_index_fn_safe =
  ({ slope := stride, max_val := ⟨ shape.val, hshape ⟩ } : LinearIntegerFunc).fun ∘ IndexSet.from_single_dimension_equiv  := by

  rw [View.from_single_dimension_index_fn_safe_eq]
  unfold LinearIntegerFunc.fun
  simp
  funext idx
  simp
  unfold NatLt.embed_nat
  simp
  rw [Nat.mul_comm]


theorem View.len_1_from_single_dimension (v: View) (hlen: v.shape.length = 1) :
  ∃ (shape stride : PosInt), v = View.from_single_dimension shape stride := by
  sorry

def View.from_linear_function (f : LinearIntegerFunc) : View :=
  View.from_single_dimension ⟨f.max_val, by sorry ⟩ ⟨f.slope, by sorry ⟩

theorem View_from_linear_function_to_linear_function (f : LinearIntegerFunc) :
  NatLt.embed_nat ∘ (View.from_linear_function f).to_index_fn_safe = f.fun ∘ IndexSet.from_single_dimension_equiv := by
  sorry

theorem View.from_linear_function_shape_eq (f : LinearIntegerFunc) :
  (View.from_linear_function f).shape = [⟨f.max_val, by sorry ⟩] := by
  unfold View.from_linear_function
  unfold View.from_single_dimension
  simp



/-- ## Unraveling -/

def unravel_unsafe (s : Shape) : Nat -> List Nat :=
  fun idx =>
    List.zipWith (fun shape stride => (idx / stride) % shape) s.toNats (Stride.from_shape s).toNats

#eval unravel_unsafe [⟨3, by simp⟩, ⟨7, by simp⟩, ⟨5, by simp⟩] 43


def unravel (s : Shape) : NatLt s.max_index -> IndexSet s :=
  fun idx =>
    ⟨ unravel_unsafe s idx, by
      unfold unravel_unsafe
      unfold Shape.is_valid_index
      simp

      have hlen : s.toNats.length ⊓ (Stride.from_shape s).toNats.length = List.length s := by
        unfold List.toNats
        simp
        have hlenstride : s.length = (Stride.from_shape s).length := by
          unfold Stride.from_shape
          rw [List.scanr_length_tail]
        rw [hlenstride]
        simp
      exists hlen

      intros i hbound
      rewrite [hlen] at hbound
      have hstride : (List.toNats s)[i] = (s)[i] := by
        exact List.toNats_getElem s i hbound
      rw [hstride]
      apply Nat.mod_lt
      exact s[i].property
    ⟩

/--
Interpretation: the input is a Nat representing an entry in the tensor; the output is the memory index
-/
def View.to_unraveled_index_fn (v : View) : NatLt v.shape.max_index -> NatLt v.max_index :=
  v.to_index_fn_safe ∘ unravel v.shape

/--
unravel is the inverse of the index function for the default view for a shape

We could make this a bit more general: if we extend unravel to all of Nat,
then this is also true for any n : Nat.
-/
theorem unravel_correct : ∀ (s : Shape) (n : NatLt s.max_index),
  (View.from_shape s).to_unraveled_index_fn n = (n : Nat) % s.max_index := by
  intro s n

  have hbnf : (View.from_shape s).to_unraveled_index_fn n = HeterogenousBase.heterogenous_base_bnf s n := by
    unfold View.to_unraveled_index_fn
    unfold unravel
    unfold unravel_unsafe
    unfold View.to_index_fn_safe
    unfold View.from_shape
    unfold HeterogenousBase.heterogenous_base_bnf
    simp
  rw [hbnf]

  exact HeterogenousBase.heterogenous_base s n


theorem unravel_correct_fn (s: Shape):
  exists
    (htype_input : NatLt (View.from_shape s).shape.max_index = NatLt s.max_index)
    (htype_output : NatLt (View.from_shape s).max_index = NatLt s.max_index) ,
     (cast htype_output) ∘ (View.from_shape s).to_unraveled_index_fn ∘ (cast htype_input) = id := by
  have htype_input : NatLt (View.from_shape s).shape.max_index = NatLt s.max_index := by
    rw [View.from_shape_shape_eq]
  have htype_output : NatLt (View.from_shape s).max_index = NatLt s.max_index := by
    rw [View.max_index_from_shape]

  exists htype_input, htype_output

  funext n
  unfold id
  unfold Function.comp
  simp

  apply Subtype.ext

  have hcast (n : NatLt (View.from_shape s).max_index): ↑ (cast htype_output n) = (n : Nat) := by
    congr
    . rw [View.max_index_from_shape]
    . simp

  rw [hcast]
  rw [unravel_correct]

  apply Nat.mod_eq_of_lt

  conv =>
    rhs
    rw [<- View.from_shape_shape_eq s]
  exact n.property

theorem unravel_correct_fn' (s: Shape):
  exists hsametype: NatLt (View.from_shape s).shape.max_index = NatLt (View.from_shape s).max_index,
     (View.from_shape s).to_unraveled_index_fn = (cast hsametype) := by

  have hsametype: NatLt (View.from_shape s).shape.max_index = NatLt (View.from_shape s).max_index := by
    rw [View.max_index_from_shape]
    rw [View.from_shape_shape_eq]
  exists hsametype

  funext n
  have hcorrect : _ := unravel_correct_fn s

  cases hcorrect with
  | intro htype_input hrest =>
    cases hrest with
    | intro htype_output hcorrect_fn =>
      have hcorrect_fn_n : _ := congrFun hcorrect_fn n
      simp at hcorrect_fn_n
      conv =>
        rhs
        rw [<- hcorrect_fn_n]

      simp


theorem unravel_correct_fn'' (s: Shape):
  exists hsametype: (View.from_shape s).shape.max_index = (View.from_shape s).max_index,
     (View.from_shape s).to_unraveled_index_fn = hsametype ▸ id := by
  have hsametype: (View.from_shape s).shape.max_index = (View.from_shape s).max_index := by
    rw [View.max_index_from_shape]
    rw [View.from_shape_shape_eq]
  exists hsametype

  funext n
  have hcorrect : _ := unravel_correct s n
  have hshape: (View.from_shape s).shape = s := by
    rw [View.from_shape_shape_eq]
  have hn_modulo_bound : ↑n % s.max_index = ↑n := by
    apply Nat.mod_eq_of_lt n.property
  rw [hn_modulo_bound] at hcorrect

  apply id_casting_lemma
  assumption


theorem unravel_correct' (s : Shape) :
  (View.from_shape s).to_unraveled_index_fn = (fun x => ⟨ x % s.max_index, by
    rw [View.max_index_from_shape]
    apply Nat.mod_lt
    exact s.max_index_posint.property
   ⟩ ) := by
  funext n
  apply Subtype.ext
  apply unravel_correct


def View.example : View := {
  shape := [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨4, by simp⟩],
  stride := [⟨12, by simp⟩, ⟨4, by simp⟩, ⟨1, by simp⟩],
  lengthEq := by simp
}
