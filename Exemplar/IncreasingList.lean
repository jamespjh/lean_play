inductive IncreasingList [LT α]: List α -> Prop where
  | nil : IncreasingList []
  | single (x : α) : IncreasingList [x]
  | cons {xs : List α } {y: α } (x : α) (h : IncreasingList (y :: xs)) (lt : y < x) : IncreasingList (x :: y :: xs)

#check IncreasingList [1, 2, 3]

example: IncreasingList [1] :=
  IncreasingList.single 1

theorem olt : 1 < 2 := by
  decide

theorem to: IncreasingList [2, 1] :=
  IncreasingList.cons 2 (IncreasingList.single 1) (by decide)

example: IncreasingList [3, 2, 1] :=
  IncreasingList.cons 3 (IncreasingList.cons 2 (IncreasingList.single 1) (by decide)) (by decide)

-- This is the type of evidence that would prove a list is increasing
def evidence_for_increasing_list [LT α ] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: ys =>
    y < x ∧ evidence_for_increasing_list (y :: ys)

-- This is the theorem that that evidence shows the list is increasing
theorem list_increasing_if_contents_are {α : Type} [LT α] {xs : List α}
    (h : evidence_for_increasing_list xs) : IncreasingList xs :=
  match xs with
  | [] => IncreasingList.nil
  | [x] => IncreasingList.single x
  | x :: _ :: _ =>
    match h with
    | ⟨lt, rest⟩ => IncreasingList.cons x (list_increasing_if_contents_are rest) lt

theorem child_list_increasing_if_parent_is {α : Type} {x: α} {ys: List α} [LT α] (h : IncreasingList (x :: ys)) : IncreasingList ys :=
  match h with
  | IncreasingList.single _ => IncreasingList.nil
  | IncreasingList.cons _ ev _ => by
    exact ev

example : IncreasingList [4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

theorem fd : IncreasingList [5, 4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

theorem td : IncreasingList [ 4, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

-- suppose we have two lists, both increasing
-- subtraction is all the elements of the first list that are not in the second
-- because the lists are increasing, we can do this by comparing the heads of the list
-- and then recursing on the tails
def subtractIncreasingList ( l1 l2 : List Nat) (h : IncreasingList l1) (h' : IncreasingList l2  ) : List Nat :=
  match l1, l2 with
  | [], _ => []
  | _, [] => l1
  | x :: xs, y :: ys =>
    -- if the head of the second list is bigger than the head of the first list, it
    -- cannot be in the first list, so we recurse on the tail of the second list
    if x < y then subtractIncreasingList (x :: xs) ys h (child_list_increasing_if_parent_is h')
    -- if the head of the second list is equal to the head of the first list, we remove it from the first list
    else if x == y then subtractIncreasingList xs ys (child_list_increasing_if_parent_is h) (child_list_increasing_if_parent_is h')
    -- if the head of the second list is smaller than the head of the first list, it might match later, so we keep it in the first list
    else if x > y then x :: subtractIncreasingList xs (y::ys) (child_list_increasing_if_parent_is h) h'
    else []

#eval subtractIncreasingList [5, 4, 3, 2, 1] [4, 2, 1] fd td
