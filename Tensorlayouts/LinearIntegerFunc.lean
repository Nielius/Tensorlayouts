import Tensorlayouts.ArithHelpers

/--
  Represents a linear function NatLt k -> Nat
-/
structure LinearIntegerFunc where
  slope : Nat
  max_val : {k : Nat // k > 1}
  deriving Repr

def LinearIntegerFunc.fun (f : LinearIntegerFunc) : (NatLt f.max_val) -> Nat :=
  fun n => f.slope * n

theorem LinearIntegerFunc.slope_eq_val_1 : ∀ (f : LinearIntegerFunc) ,
  f.slope = f.fun ⟨1, f.max_val.property ⟩ := by
  intro f
  unfold LinearIntegerFunc.fun
  simp

theorem LinearIntegerFunc.increment : ∀ (f : LinearIntegerFunc) (i : Nat) (hi : i < f.max_val - 1),
  f.fun ⟨i + 1, by sorry⟩ = f.fun ⟨i, by sorry⟩ + f.slope := by
  intro f i hi
  unfold LinearIntegerFunc.fun
  simp
  apply Nat.mul_succ

theorem LinearIntegerFunc.fun_eq_slope : ∀ (f : LinearIntegerFunc) (g : NatLt f.max_val → Nat),
  f.fun = g ↔
  ∃ hslope : (g ⟨1, f.max_val.property ⟩ = f.slope),
  (∀ (i : Nat) (hi : i < f.max_val - 1),
    g ⟨i + 1, by sorry⟩ = g ⟨i, by sorry⟩ + f.slope) := by

  intro f g
  constructor

  case mp =>
    intro hfuneq

    have hslope : (g ⟨1, f.max_val.property ⟩ = f.slope) := by
      rw [LinearIntegerFunc.slope_eq_val_1]
      apply congrFun
      exact Eq.symm hfuneq

    exists hslope

    intro i hi

    rw [← hfuneq]
    apply LinearIntegerFunc.increment
    exact hi

  case mpr =>
    intro hcond

    obtain ⟨hslope, hincr⟩ := hcond

    apply funext
    intro n

    let n' := n.val
    revert n'
    revert n

    -- TODO TODO TODO
    --
    -- 2 solutions:
    -- 1. induction on n.val (but how? create a new theorem with a slightly different framing?)
    -- 2. define induction theorem NatLt.induction (see ArithHelpers.lean)
    sorry
