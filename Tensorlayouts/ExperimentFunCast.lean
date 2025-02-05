variable {α α' β γ: Type}
variable {T : α → Type}

variable (f : α -> β)
variable (g : β -> γ)


theorem fun_cast_eq (h : α = α') : f = fun x => f (Eq.recOn h x) := by
  subst h
  simp

theorem fun_cast_compose (h : α = α') : h ▸ (g ∘ f) = (g ∘ (h ▸ f)) := by
  subst h
  simp


/- This one seems to be necessary! Often if I try `subst h ; simp` it doesn't work, because
where I need this theorem, `h` is something like `v.shape = v2.shape`, and for some reason,
the unification fails in that case. -/
theorem fun_cast_compose_higher_order (x x' : α) (f : T x -> β) (g : β -> γ) (h : x = x') : h ▸ (g ∘ f) = (g ∘ (h ▸ f)) := by
  subst h
  simp


theorem fun_cast_input_move_to_input {x x' : α} (f : T x -> β) (h : x = x') (a : T x') : (h ▸ f) a = f (h ▸ a) := by
  subst h
  simp


theorem fun_cast_input_move_to_input_composition {x x' : α} (f : T x -> β) (h : x = x')  : (h ▸ f)  = f ∘ (cast (congrArg T h.symm)) := by
  funext a
  subst h
  simp

  /- Alternative attempt; but you can't seem to get rid of using subst...
  /- Super annoying that I can't just do `apply fun_cast_input_move_to_input`! Why is the cast so different from that macro? -/
  have := fun_cast_input_move_to_input x x' f h a
  rw [this]
  simp
  /- <--- this is a super frustrating place! -/
  subst h -- this seems to be the only solution!
  simp
  -/
