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

def incex [LT α ] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | [x] => True
  | x :: y :: ys =>
    y < x ∧ incex (y :: ys)

theorem inceximpil {α : Type} [LT α] {xs : List α} (h : incex xs) : IncreasingList xs :=
  match xs with
  | [] => IncreasingList.nil
  | [x] => IncreasingList.single x
  | x :: _ :: _ =>
    match h with
    | ⟨lt, rest⟩ => IncreasingList.cons x (inceximpil rest) lt

example : IncreasingList [4, 3, 2, 1] := by
  apply inceximpil
  repeat constructor
