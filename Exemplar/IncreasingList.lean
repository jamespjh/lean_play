
-- suppose we have two lists, both increasing
-- subtraction is all the elements of the first list that are not in the second
-- because the lists are increasing, we can do this by comparing the heads of the list
-- and then recursing on the tails
-- note without proof, the function is not safe
def unsafeSubtract (l1 l2 : List Nat) : List Nat :=
  match l1, l2 with
  | [], _ => []
  | _, [] => l1
  | x :: xs, y :: ys =>
    if x < y then unsafeSubtract (x :: xs) ys
    else if x == y then unsafeSubtract xs ys
    else x :: unsafeSubtract xs (y::ys)

#eval unsafeSubtract [5, 4, 3, 2, 1] [1, 2, 3]

-- to make it safe, we define a predicate that argues that the list is increasing
-- as always the constructors are such that an instance of the predicate can only be constructed if it is true

inductive IncreasingListP [LT α]: List α -> Prop where
  | nil : IncreasingListP []
  | cons {xs : List α }  (x : α) (h : IncreasingListP xs) (lt : ∀ y ∈ xs, y < x) : IncreasingListP (x :: xs)

#check IncreasingListP [1, 2, 3]

example: IncreasingListP [1] :=
  IncreasingListP.cons 1 (IncreasingListP.nil) (by decide)

theorem olt : 1 < 2 := by
  decide

theorem to: IncreasingListP [2, 1] :=
  IncreasingListP.cons 2 (IncreasingListP.cons 1 (IncreasingListP.nil) (by decide)) (by decide)

example: IncreasingListP [3, 2, 1] :=
  IncreasingListP.cons 3 (IncreasingListP.cons 2 (IncreasingListP.cons 1 (IncreasingListP.nil) (by decide)) (by decide)) (by decide)

-- This is the type of evidence that would prove a list is increasing
def evidence_for_increasing_list [LT α ] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | x :: xs =>
    (∀ z ∈ xs, z < x) ∧ (evidence_for_increasing_list (xs))

-- This is the theorem that that evidence shows the list is increasing
theorem list_increasing_if_contents_are {α : Type} [LT α] {xs : List α}
    (h : evidence_for_increasing_list xs) : IncreasingListP xs :=
  match xs with
  | [] => IncreasingListP.nil
  | x :: _ =>
    match h with
    | ⟨lt, rest⟩  =>
      IncreasingListP.cons x (list_increasing_if_contents_are rest) lt

theorem child_list_increasing_if_parent_is {α : Type} {x: α} {ys: List α} [LT α] (h : IncreasingListP (x :: ys)) : IncreasingListP ys :=
  match h with
  | IncreasingListP.cons _ ev _ => by
    exact ev

theorem ftto : IncreasingListP [4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

def getListEvidence {α : Type} {x: α} {xs: List α} [LT α] (h: (IncreasingListP (x::xs)) ) : ∀ (y : α), y ∈ xs → y < x :=
  match h with
    | IncreasingListP.cons _ _ lt => lt

#check getListEvidence ftto

-- This is the safe version of subtracting two increasing lists
-- it uses the IncreasingListP predicate to ensure that the lists are increasing
def subtractIncreasingListA ( l1 l2 : List Nat) (h : IncreasingListP l1) (h' : IncreasingListP l2  ) : List Nat :=
  match l1, l2 with
  | [], _ => []
  | _, [] => l1
  | x :: xs, y :: ys =>
    -- if the head of the second list is bigger than the head of the first list, it
    -- cannot be in the first list, so we recurse on the tail of the second list
    if x < y then subtractIncreasingListA (x :: xs) ys h (child_list_increasing_if_parent_is h')
    -- if the head of the second list is equal to the head of the first list, we remove it from the first list
    else if x == y then subtractIncreasingListA xs ys (child_list_increasing_if_parent_is h) (child_list_increasing_if_parent_is h')
    -- if the head of the second list is smaller than the head of the first list, it might match later, so we keep it in the first list
    else x :: subtractIncreasingListA xs (y::ys) (child_list_increasing_if_parent_is h) h'

theorem fd : IncreasingListP [5, 4, 3, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

theorem td : IncreasingListP [ 4, 2, 1] := by
  apply list_increasing_if_contents_are
  repeat unfold evidence_for_increasing_list
  decide

#eval subtractIncreasingListA [5, 4, 3, 2, 1] [4, 2, 1] fd td

-- this has the flaw that the result is not guaranteed to be increasing
-- we can fix this by wrapping the result in a structure that has the IncreasingListP predicate

---- Type wrapped in structure ----

structure IncreasingList (α :Type) [LT α ] : Type where
  xs : List α
  h : IncreasingListP xs

instance [LT α] : Membership α (IncreasingList α) where
  mem l x := x ∈ l.xs

def IncreasingList.cons [LT α] (x : α) (h : IncreasingList α) (lt : ∀ y ∈ h.xs, y < x) : IncreasingList α :=
  ⟨x :: h.xs, IncreasingListP.cons x h.h lt⟩

def fttol : IncreasingList Nat :=
  ⟨[4, 3, 2, 1], ftto⟩

#eval IncreasingList.cons 5 fttol (by
  intros y hy

  skip)

theorem can_assume_r_in_or (p q : Prop) (ev: q): p ∨ (q ∧ ¬ p) := by
  cases Classical.em p
  with
    | inl h => exact Or.inl h
    | inr h' => apply Or.inr ; constructor ; assumption ; assumption

example [LT α] [Trans LT.lt LT.lt (@LT.lt α _)] (a b c : α ) (h₁ : a < b) (h₂ : b < c) : a < c :=
  trans h₁ h₂



theorem unify_ineq [LT α][Trans LT.lt LT.lt (@LT.lt α _)] (xs: List α) (x: α) (ev1: ∀ y ∈ xs, y < z) (ev2: z < x): (∀ y ∈ xs, y < x) := by
  intros y hy
  have h1 : y < z := ev1 y hy
  have h2 : z < x := ev2
  exact trans h1 h2

-- unkfun x xs someev : x::xs is increasing

theorem safe_to_append {α : Type} {m : α} [LT α] (x: α) (l : IncreasingList α) : (must_prove_to_append x l) := by

def append_to_increasing_list {α : Type} {m : α} [LT α] [Trans LT.lt LT.lt (@LT.lt α _)] (x : α) (l : IncreasingList α) (ev : m < x): IncreasingList α :=
  match l with
  | ⟨[], _⟩ => ⟨[x], IncreasingListP.cons x IncreasingListP.nil (by simp)⟩
  | ⟨l :: xs, h⟩ => ⟨x :: l :: xs, IncreasingListP.cons x h (by
    intros y hy
    -- extract the evidence from the hypothesis in the IncreasingListP
    cases h with
    | cons _ _ evv =>
      simp at hy
      cases hy with
      | inl h1 => _
      | inr h2 =>
        have h4 : y < m := evv y h2
     )⟩

instance [LT α] [ToString α] : ToString (IncreasingList α) where
  toString l := l.xs.toString

def toMaybeList (xs : List Nat) : (Option (List Nat)) :=
  match xs with
    | [] => some []
    | [x] => some [x]
    | x :: y :: ys =>
        if (y < x) then some (x :: y :: ys)
        else none

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

#eval (toMaybeIncList [5, 4, 3, 2, 1])
#eval (toMaybeIncList [1, 2, 3, 4])

instance: Coe (List Nat) (Option (IncreasingList Nat)) where
  coe xs := toMaybeIncList xs

#eval ([5, 4, 3, 2, 1] : Option (IncreasingList Nat))
#eval ([1, 2, 3, 4] : Option (IncreasingList Nat))

def subtractIncreasingList ( l1 l2 : IncreasingList Nat) : IncreasingList Nat :=
  match l1, l2 with
  | ⟨[], _⟩, _ => l1
  | _, ⟨[], _⟩ => l1
  | ⟨x :: xs, h⟩, ⟨y :: ys, h'⟩ =>
    -- if the head of the second list is bigger than the head of the first list, it
    -- cannot be in the first list, so we recurse on the tail of the second list
    if x < y then subtractIncreasingList ⟨x :: xs, h⟩ ⟨ys, child_list_increasing_if_parent_is h'⟩
    -- if the head of the second list is smaller than the head of the first list, it might match later, so we keep it in the first list
    else if h3 :  y < x then append_to_increasing_list x (subtractIncreasingList ⟨xs, child_list_increasing_if_parent_is h⟩ ⟨y::ys, h'⟩) h3
    -- if the head of the second list is equal to the head of the first list, we remove it from the first list
    else subtractIncreasingList ⟨xs, child_list_increasing_if_parent_is h⟩ ⟨ys, child_list_increasing_if_parent_is h'⟩
