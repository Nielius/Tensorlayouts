import Mathlib.Logic.Function.Basic

def F (n : Nat) (h : n = 0) := n + 1

theorem test (n : Nat) (h1 h2 : n = 0) : F n h1 = F n h2 := by
  subst h1
  rfl


structure MyPair where
  n : Nat
  m : Nat

/- This is exactly the problem I'm having! You suddenly can't use a subst anymore
if a struct is involved! And you also can't use a rewrite, because if the dependent
type. Very frustrating.-/
theorem test' (p1 : MyPair) (h1 h2 : p1.n = (0: Nat)) : F p1.n h1 = F p1.n h2 := by
  -- subst h1 -- doesn't work
  -- rw [h1] -- doesn't work

  -- working proof (but it does something else!):
  have h_eq : h1 = h2 := by
    apply proof_irrel  -- Proofs of equalities in `Prop` are always equal
  rw [h_eq]


def PosInt := { n : Nat // n > 0 }

theorem test_without_struct (f: Nat -> Nat) (x y : Nat) (h : x = y) (hx : f x > 0) (hy: f y > 0) :
  (⟨ f x , hx ⟩ : PosInt) = (⟨ f y , hy ⟩ : PosInt) := by
  simp
  subst h
  simp


theorem test_with_struct (f: Nat -> Nat) (x y : MyPair) (h : x.n = y.n) (hx : f x.n > 0) (hy: f y.n > 0) :
  (⟨ f x.n , hx ⟩ : PosInt) = (⟨ f y.n , hy ⟩ : PosInt) := by
  -- rw [h] -- doesn't work! motive type is not correct
  -- subst h -- doesn't work! invalid equality proof (this is the new problem in the struct case)
  simp -- this somehow removes the proof parts! don't know why this works though... maybe something like Subtype.ext?
  -- subst h -- still doesn't work
  rw [h] -- now I can use rewrite, because there is no proof aspect anymore

#print test_with_struct


theorem test'' (p1 : MyPair) (h1 h2 : p1.n = (0: Nat)) : F p1.n h1 = F p1.n h2 := by
  have h_rewrite : F p1.n h1 = F 0 (Eq.refl 0) := by
    apply congrArg2 F
    exact h1
    exact Eq.refl 0
  have h_rewrite' : F p1.n h2 = F 0 (Eq.refl 0) := by
    apply congrArg2 F
    exact h2
    exact Eq.refl 0
  rw [h_rewrite, h_rewrite']
  rfl

#print test



example (n : Nat) (h1 h2 : n = 0) : F n h1 = F n h2 := by
  rewrite [h1]  -- This should give "motive is dependent"


def MyVec (n : Nat) := { xs : List Nat // xs.length = n }

example (n m : Nat) (h : n = m) (v : MyVec n) : MyVec m := by
  rewrite [h]  -- This should fail with "motive is dependent"



def MyType (n : Nat) := Array.mk (List.range n)

example (n m : Nat) (h : n = m) (v : MyType n) : MyType m := by
  rewrite [h]  -- Fails with "motive is dependent"




def P (n : Nat) := Vec Nat n  -- P depends on n

example (n m : Nat) (h : n = m) (v : P n) : P m := by
  rewrite [h]  -- This fails with "motive is dependent"


def NT := { n : Nat // n > 0 }
example (n m : NT) (h: n = m) : n = m := by
  rewrite [h]






def P (n : Nat) := n = 2



example (n : Nat) (h : n = 2) : P n := by
  rewrite [h]  -- Fails with "motive is dependent"
