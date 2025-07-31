
-- suppose we have two lists, both increasing
-- subtraction is all the elements of the first list that are not in the second
-- because the lists are increasing, we can do this by comparing the heads of the list
-- and then recursing on the tails
-- note without proof, the function is not safe
def unsafeSubtract {α : Type} [Ord α] (l1 l2 : List α) : List α :=
  match l1, l2 with
  | [], _ => [] -- A
  | _, [] => l1 -- B
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => unsafeSubtract (x :: xs) ys -- C
    | .eq => unsafeSubtract xs ys -- D
    | .gt => x :: unsafeSubtract xs (y :: ys) -- E

-- The alphabetic tags will be used to refer to the cases in the proof below

def fives : List Nat := [5, 4, 3, 2, 1]
def threes : List Nat := [3, 2, 1]

#eval unsafeSubtract fives threes

-- We can wrap the lists with an option or exception to handle the problem

def isIncreasing {α : Type} [LT α] [DecidableRel (@LT.lt α _)] (xs : List α) : Bool :=
  match xs with
  | [] => true -- A
  | [_] => true -- B
  | x :: y :: ys =>
    if y < x then isIncreasing (y :: ys) -- C
    else false --D

#eval isIncreasing fives

def fives_back := [1, 2, 3, 4, 5]
#eval isIncreasing fives_back

def toList? {α : Type} [LT α] [DecidableRel (@LT.lt α _)] (xs : List α) : Option (List α) :=
  if isIncreasing xs then
    some xs
  else
    none

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

-- Now we could assert that the lists have the right property,
-- Our work still has the flaw that the result is not guaranteed to be increasing

-- Let's try to prove things about our proposition

-- We'll make some lemmas that will be useful to prove things about our functions

theorem child_list_increasing_if_parent_is {α : Type} {x: α} [LT α] {ys: List α} (h : IncreasingListP (x :: ys)) : IncreasingListP ys :=
  match h with
  | IncreasingListP.single _ => IncreasingListP.nil
  | IncreasingListP.cons _ ev _ => by
    exact ev

theorem unfold_increasing_list_once {α : Type} {x: α} {y: α } {ys: List α} [LT α] (h : IncreasingListP (x :: y :: ys)) : (y < x) ∧ IncreasingListP (y :: ys) :=
  match h with
  | IncreasingListP.cons _ ev lt => by
    exact ⟨lt, ev⟩

theorem head_is_bigger_than_all_the_rest  {α : Type}  [LT α] [Trans LT.lt LT.lt (@LT.lt α _)] {xs: List α} : ∀ x, IncreasingListP (x :: xs) ->  ∀ z ∈ xs, z < x := by
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

-- And about our functions

theorem unsafe_subtract_generates_subset {α : Type} [Ord α] (l1 : List α) : ∀ l2, (unsafeSubtract l1 l2) ⊆ l1 := by
  induction l1 with
  | nil => intro l2; unfold unsafeSubtract; simp -- A
  | cons z zs hyp1 =>
    intro l2
    induction l2 with
    | nil => unfold unsafeSubtract; simp -- B
    | cons w ws hyp2 =>
      unfold unsafeSubtract
      match compare z w with
      | .lt => exact hyp2 -- C
      | .eq => simp [hyp1 ws] -- D
      | .gt => simp [hyp1 (w::ws)] -- E

theorem unsafe_subtract_generates_increasing {α : Type} [Ord α] [LT α] [Trans LT.lt LT.lt (@LT.lt α _)]
  {l1 : List α} (h : IncreasingListP l1) : ∀ l2, IncreasingListP (unsafeSubtract l1 l2) := by
  induction l1 with
  | nil => unfold unsafeSubtract; simp; exact IncreasingListP.nil --A
  | cons z zs hyp1 =>
    intro l2
    induction l2 with
    | nil => unfold unsafeSubtract; exact h --B
    | cons w ws hyp2 =>
      unfold unsafeSubtract
      match compare z w with
      | .lt => exact hyp2 -- C
      | .eq => exact hyp1 (child_list_increasing_if_parent_is h) ws --D
      | .gt =>
        simp [child_list_increasing_if_parent_is h] at hyp1;
        generalize q : unsafeSubtract zs (w :: ws) = qq
        cases qq with
        | nil => exact IncreasingListP.single z -- Part of (E) - occurs when neither zs nor l2 is empty, but they are equal
        | cons qh qt =>
          have k := unsafe_subtract_generates_subset zs (w::ws)
          have j := hyp1 (w::ws)
          have t := head_is_bigger_than_all_the_rest z h
          rw [q] at j k
          have qhmem : qh ∈ zs := by
            apply k
            apply List.mem_cons_self
          have jj := t qh qhmem
          exact IncreasingListP.cons z j jj -- E

theorem is_increasing_list_is_increasing {α : Type} [LT α] [DecidableRel (@LT.lt α _)] {xs : List α} : isIncreasing xs -> (IncreasingListP xs) := by
  induction xs with
  | nil => intro; exact IncreasingListP.nil -- A
  | cons x xs ih =>
    intro h
    match xs with
    | [] => exact IncreasingListP.single x -- B
    | y :: ys =>
      unfold isIncreasing at h
      simp at h
      cases h with | intro lt rest =>
      exact IncreasingListP.cons x (ih rest) lt -- C
      -- D is false by assumption

-- And still need to prove the function correct, :
-- it has none of the l2s in the answer
-- and all of the l1s that are not in l2

-- We can now combine the evidence and data into a structure and present functions that treat it as a single type--

structure IncreasingList (α :Type) [LT α ] : Type where
  xs : List α
  h : IncreasingListP xs

instance [LT α] : Membership α (IncreasingList α) where
  mem l x := x ∈ l.xs

def IncreasingList.cons {α : Type} [LT α] (x : α) (y:α) (ys: List α) (h : IncreasingListP (y::ys)) (lt : y < x) : IncreasingList α :=
  ⟨ x :: y :: ys, IncreasingListP.cons x h lt ⟩

instance [LT α] [ToString α] : ToString (IncreasingList α) where
  toString l := l.xs.toString ++ " (proved increasing)"

def toIncreasingList? (xs: List α) [LT α] [DecidableRel (@LT.lt α _)] : (Option (IncreasingList α )) :=
  if h : isIncreasing xs then
    let z: IncreasingListP xs := is_increasing_list_is_increasing h
    some ⟨xs, z⟩
  else
    none

def subtractIncreasingList {α : Type} [Ord α] [LT α] [Trans LT.lt LT.lt (@LT.lt α _)] (l1 : IncreasingList α) (l2 : IncreasingList α) : IncreasingList α :=
  let newList := unsafeSubtract l1.xs l2.xs
  let h := unsafe_subtract_generates_increasing l1.h l2.xs
  ⟨newList, h⟩

instance: Coe (List Nat) (Option (IncreasingList Nat)) where
  coe xs := toIncreasingList? xs

#eval toIncreasingList? fives
#eval toIncreasingList? fives_back
#eval toIncreasingList? [7, 4, 1]

#eval (fives_back : Option (IncreasingList Nat))
#eval (fives : Option (IncreasingList Nat))

-- run the subtraction in a monadic context
#eval do pure (subtractIncreasingList (← toIncreasingList? fives) (←threes))
