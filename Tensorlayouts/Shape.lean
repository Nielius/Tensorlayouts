import Aesop
import Tensorlayouts.ArithHelpers
import Mathlib.Data.List.Basic -- needed for e.g. List.scanr_nil; this is part of simp
import Mathlib.Data.List.Zip -- needed for List.zipWith_map_right

import Mathlib.Tactic.Zify
open Mathlib.Tactic.Zify (zify)

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



#eval Stride.from_shape [⟨2, by simp⟩, ⟨3, by simp⟩, ⟨54, by simp⟩]


/- ## Indexing for shapes -/

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
    (List.zipWith (fun shape stride => (x / stride % shape)) s.toNats (Stride.from_shape s).toNats).sum


example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
calc a = b + 1 := H1
     _ = c + 1 := by rw [H2]

-- calc is also available in tactic mode. You can leave ?_s to create a new goal:

example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 := by
  calc
    a = b + 1 := ?_
    _ = c + 1 := ?_
  · exact H1
  · rw [H2]




/--
A representation of a number in a heterogeneous base consisting of two digits,
including the overflow to what would be the next digit.

This structure is convenient for the proof of the correctness of the heterogenous base,
because it has just enough information to do the induction step.
-/
structure PairBaseRepresentation where
  overflow: Nat
  digit2: Nat
  digit1: Nat
  size2: PosInt
  size1: PosInt

def PairBaseRepresentation.to_nat : PairBaseRepresentation -> Nat :=
  fun p =>
    p.overflow + p.size1 * p.digit2 + p.digit1

def PairBaseRepresentation.from_nat (size2 size1 : PosInt) : Nat -> PairBaseRepresentation :=
  fun n =>
    let digit2 := (n / size1) % size2
    let digit1 := n % size1
    let overflow := n - (n % (size2 * size1))
    {overflow := overflow, digit2 := digit2, digit1 := digit1, size2 := size2, size1 := size1}

set_option pp.parens true

theorem PairBaseRepresentation.from_nat_to_nat : ∀ (size2 size1 : PosInt) (n : Nat),
  PairBaseRepresentation.to_nat (PairBaseRepresentation.from_nat size2 size1 n) = n := by
  intro size2 size1 n
  unfold PairBaseRepresentation.from_nat
  unfold PairBaseRepresentation.to_nat
  simp

  have h : size1 * ((n / size1) % size2) + n % size1 = n % (size2 * size1) := by
    calc
          size1 * ((n / size1) % size2) + n % size1
        = size1 * ((n % (size1 * size2)) / size1) + n % size1 := ?_
      _ = size1 * ((n % (size2 * size1)) / size1) + n % size1 := ?_
      _ = size1 * ((n % (size2 * size1)) / size1) + (n % (size2 * size1)) % size1 := ?_
      _ = n % (size2 * size1) := Nat.div_add_mod (n % (size2 * size1)) size1

    . suffices hsuf : ((n / size1) % size2) = (n % (size1 * size2)) / size1 by
        simp
        rw [hsuf]
      rw [Nat.mod_mul_right_div_self]
    . conv =>
        pattern n % (↑size1 * ↑size2)
        rw [Nat.mul_comm]
    . suffices hsuf : (n % (size2 * size1)) % size1 = n % size1 by
        omega
      exact Nat.mod_mul_left_mod n ↑size2 ↑size1

  rw [<- h]
  rw [Nat.add_assoc]
  rw [Nat.sub_add_cancel]


  calc
         (↑size1 * ((n / ↑size1) % ↑size2)) + (n % ↑size1)
       ≤ (↑size1 * ((n / ↑size1)))          + (n % ↑size1) := ?_
    _  ≤ n := ?_
  . have htrivial_ineq: ((n / ↑size1) % ↑size2) ≤ (n / ↑size1) := by apply Nat.mod_le
    simp
    apply Nat.mul_le_mul_left
    assumption
  . rw [Nat.div_add_mod]



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
    simp
    omega

  case cons shape_head shape_tail tail_ih =>
    intro x
    let xrem := x % Shape.max_index shape_tail
    let xdiv := x / Shape.max_index shape_tail

    have hxdiv_eq : Shape.max_index shape_tail * xdiv + xrem = x := by
      unfold xrem xdiv
      exact Nat.div_add_mod x (Shape.max_index shape_tail)

    have hxrem_lt : xrem < Shape.max_index shape_tail := by
      apply Nat.mod_lt
      exact (Shape.max_index_posint shape_tail).property

    have hxrem_ih : heterogenous_base_bnf shape_tail xrem = xrem % Shape.max_index shape_tail := by
      apply tail_ih

    rw [Nat.mod]

    have hasdf : (Shape.max_index shape_tail * xdiv + xrem) % Shape.max_index (shape_head :: shape_tail)
    = Shape.max_index shape_tail * (xdiv / shape_head) % Shape.max_index (shape_head :: shape_tail) + xrem % Shape.max_index shape_tail := by




    conv =>
      rhs
      rw [<- hxdiv_eq]



    have Shape.max_index (shape_head :: shape_tail)





    rw [List.toNats_cons]
    rw [Stride.from_shape_cons_max_index]
    simp
    rw [List.toNats_cons]
    rw [List.zipWith_cons_cons]

    rw [List.sum_cons]

    rw [← hxdiv_eq]

    rw [tail_ih xrem]
    simp [Shape.max_index_posint]
    swap




    rw [← hxdiv_eq]






    /- Maybe this case distinction is not necessary? -/
    by_cases x < Shape.max_index shape_tail

    case pos hnewbound =>
      rw [List.toNats_cons]
      rw [Stride.from_shape_cons_max_index]
      simp
      rw [List.toNats_cons]
      rw [List.zipWith_cons_cons]

      rw [List.sum_cons]
      rw [tail_ih]
      simp [Shape.max_index_posint]

      rw [Shape.max_index_cons] at hbound
      conv =>
        pattern (x / _ % _)
        rw [← Nat.mod_mul_right_div_self]
      rw [Nat.mod_eq_of_lt]
      swap
      rw [Nat.mul_comm]
      assumption
      apply Nat.div_eq_of_lt; all_goals assumption

    case neg hnewbound =>
      rw [List.toNats_cons]
      rw [Stride.from_shape_cons_max_index]
      simp
      rw [List.toNats_cons]
      rw [List.zipWith_cons_cons]





    sorry

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
    List.zipWith (fun shape stride => (idx / stride) % shape) s.toNats (Stride.from_shape s).toNats

#eval unravel_unsafe [⟨3, by simp⟩, ⟨7, by simp⟩, ⟨5, by simp⟩] 43


-- TODO: this is not quite correct, because we are taking a modulo at the very last component as well, whereas we shouldn't
def unravel (s : Shape) : Nat -> IndexSet s :=
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

def View.to_unraveled_index_fn (v : View) : Nat -> Nat :=
  v.to_index_fn_safe ∘ unravel v.shape

/--
unravel is the inverse of the index function for the default view for a shape
-/
theorem unravel_correct_other : ∀ (s : Shape) (n : Nat),
  n < s.max_index -> (View.from_shape s).to_unraveled_index_fn n = n := by
  intro s n hbound
  unfold View.to_unraveled_index_fn
  unfold unravel
  unfold unravel_unsafe
  have shape_eq : (View.from_shape s).shape = s := by
    rw [View.from_shape_shape_eq]
  simp [shape_eq]
  -- now we've nicely unfolded the unravelling function

  unfold View.from_shape
  unfold View.to_index_fn_safe

  have stride_eq : (View.from_shape s).stride = Stride.from_shape s := by
    rw [View.from_shape_stride_eq]
  simp [stride_eq]

  -- introduce variable for strides
  let strides := Stride.from_shape s
  replace strides_eq : strides = Stride.from_shape s := by rfl

  conv in (occs := 1 2) (Stride.from_shape s) =>
     all_goals rw [← strides_eq]

  -- now do the inner product
  unfold List.inner_prod
  rw [List.zipWith_zipWith_right]
  rw [List.zipWith3_same_mid]

  sorry -- we have now reduced the problem to simple arithmetic


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
