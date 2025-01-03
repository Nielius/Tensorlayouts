namespace FunextExperiment
/--
  Experiment with functional equality
  --- does it work as I would expect? Yes!
-/

def OnlyTwoNumbers : Type := {x : Nat // x < 2}

def square : OnlyTwoNumbers → Nat := fun x => x.val * x.val

def identity : OnlyTwoNumbers → Nat := fun x => x.val

theorem only_two_numbers_one_or_two : ∀ (x : OnlyTwoNumbers), x.val = 0 ∨ x.val = 1 := by
  intro x
  have h : x.val < 2 := by
    exact x.property
  omega


example (functional_eq_ex : square = identity) : square = identity := by
  funext x
  simp [square, identity]
  have h := only_two_numbers_one_or_two x
  cases h
  case h.inl h0 =>
    simp [h0]
  case h.inr h1 =>
    simp [h1]

end FunextExperiment
