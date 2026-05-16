import LearnLean
import Mathlib

def safeGet {α} (l : List α) (n : Nat) : Option α :=
  match l with
  | [] => none
  | x::xs => match n with
    | Nat.zero => some x
    | Nat.succ k => safeGet xs k

theorem safeGet_eq (l : List α) (n : Nat) : safeGet l n = l[n]? := by
  revert n
  induction l with
  | nil => intro n
           rfl
  | cons x xs ih => intro n
                    induction n with
                    | zero => rfl
                    | succ k => unfold safeGet
                                simp
                                rw[ih]
