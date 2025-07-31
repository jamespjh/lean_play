
-- suppose we have two lists, both increasing
-- subtraction is all the elements of the first list that are not in the second
-- because the lists are increasing, we can do this by comparing the heads of the list
-- and then recursing on the tails
-- note without proof, the function is not safe
def unsafeSubtract {α : Type} [Ord α] (l1 l2 : List α) : List α :=
  match l1, l2 with
  | [], _ => []
  | _, [] => l1
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => unsafeSubtract (x :: xs) ys
    | .eq => unsafeSubtract xs ys
    | .gt => x :: unsafeSubtract xs (y :: ys)

#eval unsafeSubtract [5, 4, 3, 2, 1] [1, 2, 3]

-- We can wrap the lists with an option or exception to handle the problem

def toMaybeList {α : Type} [LT α] [DecidableRel (@LT.lt α _)] (xs : List α) : Option (List α) :=
  match xs with
  | [] => some []
  | [x] => some [x]
  | x :: y :: ys =>
      if y < x then some (x :: y :: ys)
      else none

-- But Lean idiom resolves this more powerfully, by proving the list is as it should be.

-- We define a predicate that argues that the list is increasing
-- The constructors are such that an instance of the predicate can only be constructed if it is true

inductive IncreasingListP [LT α]: List α -> Prop where
  | nil : IncreasingListP []
  | single (x : α) : IncreasingListP [x]
  | cons (x : α) (h : IncreasingListP (y::xs)) (lt : y < x) : IncreasingListP (x :: y :: xs)

#check IncreasingListP [1, 2, 3]

example: IncreasingListP [1] := IncreasingListP.single 1

theorem olt : 1 < 2 := by
  decide

theorem to: IncreasingListP [2, 1] :=
  IncreasingListP.cons 2 (IncreasingListP.single 1) (by decide)

example: IncreasingListP [3, 2, 1] :=
  IncreasingListP.cons 3 (IncreasingListP.cons 2 (IncreasingListP.single 1) (by decide)) (by decide)

-- This is the type of evidence that would prove a list is increasing
def evidence_for_increasing_list [LT α ] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | [x] => True
  | x :: y :: xs =>
    (y < x) ∧ (evidence_for_increasing_list (y :: xs))

-- This is the theorem that that evidence shows the list is increasing
theorem list_increasing_if_contents_are {α : Type} [LT α] {xs : List α}
    (h : evidence_for_increasing_list xs) : IncreasingListP xs :=
  match xs with
  | [] => IncreasingListP.nil
  | [x] => IncreasingListP.single x
  | x :: _ :: _ =>
    match h with
    | ⟨lt, rest⟩  =>
      IncreasingListP.cons x (list_increasing_if_contents_are rest) lt

theorem child_list_increasing_if_parent_is {α : Type} {x: α} [LT α] (ys: List α) (h : IncreasingListP (x :: ys)) : IncreasingListP ys :=
  match h with
  | IncreasingListP.single _ => IncreasingListP.nil
  | IncreasingListP.cons _ ev _ => by
    exact ev

theorem unfold_increasing_list_once {α : Type} {x: α} {y: α } {ys: List α} [LT α] (h : IncreasingListP (x :: y :: ys)) : (y < x) ∧ IncreasingListP (y :: ys) :=
  match h with
  | IncreasingListP.cons _ ev lt => by
    exact ⟨lt, ev⟩

theorem head_is_bigger_than_all_the_rest  {α : Type}  [LT α] [Trans LT.lt LT.lt (@LT.lt α _)] (xs: List α) : (x: α) -> IncreasingListP (x :: xs) ->  ∀ z ∈ xs, z < x := by
  induction xs with
  | nil => intro x h z hz; cases hz
  | cons y ys ih =>
    intro x h z hz
    have j := unfold_increasing_list_once h
    cases j with
    | intro l r
    have n := ih y r z
    cases hz with
    | head => exact l
    | tail s w => exact trans (n w) l

theorem ftto : IncreasingListP [4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

theorem fd : IncreasingListP [5, 4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

theorem td : IncreasingListP [ 4, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

-- Now we can assert that the lists have the right property, but this has the flaw that the result is not guaranteed to be increasing

-- Let's try to prove things about the unsafe function

theorem member_lemma_lists_one : a ∈ xs -> a ∈ x::xs := by
  intro h
  simp
  exact Or.inr h

theorem unsafe_subtract_generates_subset {α : Type} [Ord α] (l1 : List α) : ∀ l2, (unsafeSubtract l1 l2) ⊆ l1 := by
  induction l1 with
  | nil => intro l2; unfold unsafeSubtract; simp
  | cons z zs hyp1 =>
    intro l2
    induction l2 with
    | nil => unfold unsafeSubtract; simp
    | cons w ws hyp2 =>
      unfold unsafeSubtract
      match compare z w with
      | .lt => exact hyp2
      | .eq => simp [hyp1 ws]
      | .gt => simp [hyp1 (w::ws)]

theorem unsafe_subtract_generates_increasing {α : Type} [Ord α] [LT α] [Trans LT.lt LT.lt (@LT.lt α _)]
  (l1 : List α) (h : IncreasingListP l1) : ∀ l2, IncreasingListP (unsafeSubtract l1 l2) := by
  induction l1 with
  | nil => unfold unsafeSubtract; simp; exact IncreasingListP.nil
  | cons z zs hyp1 =>
    intro l2
    induction l2 with
    | nil => unfold unsafeSubtract; exact h
    | cons w ws hyp2 =>
      unfold unsafeSubtract
      match compare z w with
      | .lt => exact hyp2
      | .eq => exact hyp1 (child_list_increasing_if_parent_is zs h) ws
      | .gt =>
        simp [child_list_increasing_if_parent_is zs h] at hyp1;
        generalize q : unsafeSubtract zs (w :: ws) = qq
        cases qq with
        | nil => exact IncreasingListP.single z
        | cons qh qt =>
          have k := unsafe_subtract_generates_subset zs (w::ws)
          have j := hyp1 (w::ws)
          have t := head_is_bigger_than_all_the_rest zs z h
          rw [q] at j k
          have qhmem : qh ∈ zs := by
            apply k
            apply List.mem_cons_self
          have jj := t qh qhmem
          exact IncreasingListP.cons z j jj



---- With these theorems, we can make a type wrapping the list with the method wrapped in structure ----

structure IncreasingList (α :Type) [LT α ] : Type where
  xs : List α
  h : IncreasingListP xs

instance [LT α] : Membership α (IncreasingList α) where
  mem l x := x ∈ l.xs

def IncreasingList.cons {α : Type} [LT α] (x : α) (y:α) (ys: List α) (h : IncreasingListP (y::ys)) (lt : y < x) : IncreasingList α :=
  ⟨ x :: y :: ys, IncreasingListP.cons x h lt ⟩

instance [LT α] [ToString α] : ToString (IncreasingList α) where
  toString l := l.xs.toString

def toMaybeIncList (xs: List Nat) : (Option (IncreasingList Nat)) :=
  match xs with
  | [] => some ⟨[], IncreasingListP.nil⟩
  | [x] => some ⟨[x], IncreasingListP.single x⟩
  | x :: xs =>
    let rest := toMaybeIncList xs
    match rest with
    | some ⟨ y :: ys, h ⟩ =>
      if h2 : y < x then
        some ⟨ x :: y :: ys, IncreasingListP.cons x h h2 ⟩
      else none
    | some ⟨ [], _ ⟩ => some ⟨ [x], IncreasingListP.single x ⟩ -- does not occur, but needed as lean doesn't know
    | none => none

instance: Coe (List Nat) (Option (IncreasingList Nat)) where
  coe xs := toMaybeIncList xs

#eval (toMaybeIncList [5, 4, 3, 2, 1])
#eval (toMaybeIncList [1, 2, 3, 4])

#eval ([5, 4, 3, 2, 1] : Option (IncreasingList Nat))
#eval ([1, 2, 3, 4] : Option (IncreasingList Nat))
