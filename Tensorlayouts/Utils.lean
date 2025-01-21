@[simp] theorem List.zipWith_replicate_right {b : β} {f : α → β → γ} {l : List α} :
    List.zipWith f l (List.replicate l.length b) = List.map (fun x => f x b) l := by
    induction l
    case nil =>
      simp
    case cons hd tl ih =>
      simp
      rw [List.replicate_succ]
      rw [List.zipWith_cons_cons]
      rw [ih]
