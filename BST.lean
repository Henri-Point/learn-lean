import LearnLean
import Mathlib

-- The binary tree must be defined as a dependent type so that the condition on the tree
-- can be encoded in the type itself.
inductive BST (α : Type) [LinearOrder α]: α → α → Type where
  | nil: BST α lo hi
  | cons: (n : α) → BST α lo n → BST α n hi → (lo < n) → (n < hi) → BST α lo hi

def insert [LinearOrder α] (n : α) (bst: BST α lo hi) (hlo : lo < n) (hhi : n < hi) : BST α lo hi :=
  match bst with
  | BST.nil => BST.cons n BST.nil BST.nil hlo hhi
  | BST.cons m l r hln hhn => match h : compare n m with
                              | Ordering.lt => BST.cons m (insert n l hlo (by exact compare_lt_iff_lt.mp h)) r hln hhn
                              | Ordering.gt => BST.cons m l (insert n r (by exact compare_gt_iff_gt.mp h) hhi) hln hhn
                              | Ordering.eq => bst

def member [LinearOrder α] (n : α) (bst: BST α lo hi) : Bool :=
  match compare lo n, compare n hi with
  -- There is a subtle bug here. If you have equality in your bounds, then
  -- you should also short circuit and return false immediately.
  -- Implement this at one point.
  | Ordering.gt, _ => false
  | _, Ordering.gt => false
  | _, _ => match bst with
         | BST.nil => false
         | BST.cons m l r _ _ => match compare n m with
                                 | Ordering.lt => member n l
                                 | Ordering.gt => member n r
                                 | Ordering.eq => true

def toSortedList [LinearOrder α] (bst: BST α lo hi) : List α :=
  match bst with
  | BST.nil => []
  | BST.cons n l r _ _ => (toSortedList l) ++ [n] ++ (toSortedList r)

theorem bst_bounds [LinearOrder α] (bst: BST α lo hi) :
    n ∈ (toSortedList bst) → (lo < n) ∧ (n < hi) := by
      induction bst with
      | nil => simp [toSortedList]
      | cons m l r hlo hhi ihl ihr => simp [toSortedList]
                                      rename_i lo' hi'
                                      have hmb : (lo' < m) ∧ (m < hi') := by simp [hhi, hlo]
                                      intro h
                                      rcases h with hl | hm | hr
                                      · have hmi : (n < hi') := by simp [hl] at ihl; exact lt_trans ihl.2 hhi
                                        simp [hl] at ihl
                                        simp [ihl, hmi]
                                      · rw [← hm] at hmb
                                        simp [hmb]
                                      · simp [hr] at ihr
                                        have hml : (lo' < n) := by exact lt_trans hlo ihr.1
                                        simp [hml, ihr]


theorem toSortedList_is_correct [LinearOrder α] (bst: BST α lo hi) :
    (toSortedList bst).Pairwise (· < ·) := by
      induction bst with
      | nil => simp[toSortedList]
      | cons n l r hlo hhi ihl ihr => simp [toSortedList]
                                      rw [List.pairwise_append]
                                      simp [List.pairwise_cons]
                                      simp [ihr, ihl]
                                      rename_i lo' hi'
                                      constructor
                                      · intro b h
                                        simp[bst_bounds r h]
                                      · intro b
                                        intro h
                                        simp [bst_bounds l h]
                                        intro c
                                        intro hc
                                        have hcb : (n < c) := by simp [bst_bounds r hc]
                                        have hbb : (b < n) := by simp [bst_bounds l h]
                                        exact lt_trans hbb hcb
