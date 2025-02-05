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
  rw [Subtype.mk.injEq] -- this removes the proof parts! and therefore, we can use rewrite. But this approach is not always possible.
  rw [h] -- now I can use rewrite, because there is no proof aspect anymore


section DependentRewrite

variable {Shape: Type}
variable {N : Shape -> Type}


variable (s s' : Shape)
variable (f : ∀ (s: Shape), N s → Nat)

theorem dependent_rewrite_works (h : s = s') (x : N s) : f s x = f s' (cast (congrArg N h) x) := by
  subst h
  rfl

#print dependent_rewrite_works

#check @Eq.rec Shape s (fun s' h ↦ f s x = f s' (cast (congrArg N h) x)) (Eq.refl (f s x)) s' h : f s x = f s' (cast ⋯ x)

end DependentRewrite
