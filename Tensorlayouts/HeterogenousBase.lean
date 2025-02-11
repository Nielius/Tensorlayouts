import Tensorlayouts.Shape

/- ## Heterogenous base -/
namespace HeterogenousBase

/-- back-and-forth in the heterogeneous base; mostly a helper function -/
def heterogenous_base_bnf (s : Shape) : Nat -> Nat :=
  fun x =>
    (Stride.from_shape s).inner_prod
    (List.zipWith (fun shape stride => (x / stride % shape)) s (Stride.from_shape s))


theorem heterogenous_base_bnf_cons : ∀ (shead : PosInt) (stail : Shape) (x : Nat),
  heterogenous_base_bnf (shead :: stail) x =
  (Shape.max_index_posint stail * (x / Shape.max_index_posint stail % shead)) +
  heterogenous_base_bnf stail x := by
  intro shead stail x
  unfold heterogenous_base_bnf
  rw [Stride.from_shape_cons_eq_max_index]
  simp only [List.map_cons, List.zipWith_cons_cons]
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
