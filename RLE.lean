import LearnLean
import Mathlib

def rle [DecidableEq α] (l : List α) : (List (Nat × α)) :=
  l.foldl (fun acc x =>
  match acc.getLast? with
  | none => List.append acc [(1,x)]
  | some (n,a) => if x==a then acc.set (acc.length -1) (n+1, x) else List.append acc [(1,x)]
  ) []

#eval rle [1,1,1,2,3,3,4,1,1]

def decode_rle [DecidableEq α] (c : List (Nat × α)) : (List α) :=
  match c with
  | [] => []
  | (n,a)::cs => if n == 0 then decode_rle cs else List.append (List.replicate n a) (decode_rle cs)

#eval decode_rle [(3, 1), (1, 2), (2, 3), (1, 4), (2, 1)]

-- The function decode_rle traverses the list front to back. The induction in rle_roundtrip needs it to be the other way around. This is why this lemma is neccessary.
theorem decode_distributivity [DecidableEq α] (xs: List (Nat × α)) (ys: List (Nat × α)) :
  decode_rle (xs ++ ys) = decode_rle xs ++ decode_rle ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [decode_rle]
                    rw[ih]
                    split
                    rfl
                    rw [List.append_assoc]


theorem set_last_eq_dropLast_append (l : List α) (v : α) (h : l ≠ []) :
  l.set (l.length - 1) v = l.dropLast ++ [v] := by
  induction l with
  | nil => contradiction
  | cons x xs hl => simp
                    cases xs with
                    | nil => simp
                    | cons y ys => simp at hl
                                   simp [hl]


-- TODO: Finish this one. You will need a new lemma in order to close this out.
theorem rle_roundtrip [DecidableEq α] (acc : List (Nat × α)) (l : List α) :
  decode_rle (l.foldl (fun acc x =>
    match acc.getLast? with
    | none => List.append acc [(1,x)]
    | some (n,a) => if x==a then acc.set (acc.length -1) (n+1, x) else List.append acc [(1,x)]
    ) acc) = (decode_rle acc) ++ l := by
    induction l generalizing acc with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons]
                      rcases hr : acc.getLast? with none | ⟨n, a⟩
                      ·  simp
                         have h := ih (acc ++ [(1, x)])
                         rw [decode_distributivity] at h
                         simp [decode_rle] at h
                         simp [h]
                      ·  simp
                         cases ha : a==x with
                         |true => have h := ih (acc.dropLast ++ [(n+1, x)])
                                  rw [decode_distributivity] at h
                                  simp [decode_rle] at h
                                  have ha' := eq_of_beq ha
                                  simp [ha']
                                  have hacc := hr
                                  have hne : acc ≠ [] := by intro hempty; simp [hempty] at hacc
                                  have hl := set_last_eq_dropLast_append acc (n+1,x) hne
                                  simp [hl]
                                  simp [h]
                                  simp [← List.getLast_eq_iff_getLast?_eq_some hne] at hacc
                                  have hdl : acc = acc.dropLast ++ [(n,x)] := by conv_lhs => rw [← List.dropLast_append_getLast hne]; rw [hacc, ha']
                                  rw [hdl]
                                  simp [decode_distributivity]
                                  simp [decode_rle]
                                  cases hn : n==0 with
                                  | true => have hn' := eq_of_beq hn
                                            simp [hn']
                                  | false => have hn' := not_eq_of_beq_eq_false hn
                                             simp [hn']
                                             simp [List.replicate_succ']
                         |false => have h := ih (acc ++ [(1, x)])
                                   rw [decode_distributivity] at h
                                   simp [decode_rle] at h
                                   have hacc := hr
                                   have ha' := not_eq_of_beq_eq_false ha
                                   simp [ne_comm] at ha'
                                   simp [ha']
                                   simp [h]
