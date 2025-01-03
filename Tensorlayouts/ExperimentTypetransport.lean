

variable (α β γ : Type) (h : α = β) (f1 : α → γ)


#check h ▸ f1

def f2 : β → γ := h ▸ f1

#check Eq.refl (α → γ)

theorem asdf : (h : α = β) → (α → γ) = (β → γ) := by
  intro h
  rw [h]

#check fun α β γ h ↦ Eq.mpr (id (congrArg (fun _a ↦ (_a → γ) = (β → γ)) h)) (Eq.refl (β → γ))
#check fun α β γ h ↦ Eq.mpr (congrArg (fun _a ↦ (_a → γ) = (β → γ)) h) (Eq.refl (β → γ))

#print asdf





(α → γ) = (β → γ)
