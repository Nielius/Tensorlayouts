variable (α α' β γ: Type)

variable (f : α -> β)
variable (g : β -> γ)

variable (T : α → Type)

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


#print fun_cast_compose
