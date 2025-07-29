def hello := "world"

example := 1 + 2

example : Nat := 1+2 *5

example : String := "hello" ++ "world"

example := String.append "a" (if 1>2 then "b" else "c")

def m := 1

#eval m+1

#check m

#eval (1 - 2 : Nat)

#eval (1 -2 : Int)

#check (1 - 2 : Int)

def lean : String := "lean"

#check lean

def add1 n := n+1

#eval add1 2

def add1b (n : Nat) : Nat := n+1
#eval add1b 2

#check add1b

def add (a: Nat) (b:Nat) : Nat := a + b

def k : Nat := 2

#eval k

def z :  (2 = 3) := rfl
#check add

#eval (2 = 2)
#check (2 = 2)

#check (True)
#check (True : Bool)
#eval (True : Bool)
#eval (True)
#check (decide)

def x (a: Nat) : Nat := a+1

#eval x 3

#check add

def Str : Type := String

#check Str

#check Nat

abbrev N : Type := Nat

def thirtyNine : N := 39

#check 1.2

structure Point where
  x : Float
  y : Float
deriving Repr

#check Point
def p : Point := { x := 1.0, y := 2.0 }
#check p
#eval p
#eval p.x
#check ({ x := 0.0, y := 0.0 } : Point)
#check { x := 0.0, y := 0.0 : Point}

def zeroX (p : Point) : Point :=
  { p with x := 0 }
#eval zeroX p

#check (Point.mk)
-- Point.mk : Float → Float → Point

#eval "one string".append " and another"

#eval String.append "one string" " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

#check fun (_ : Nat → Option Nat) =>
  match _ with
  | 0 => none
  | n + 1 => some n

inductive myList : Type → Type where
  | nil : myList α
  | cons : α → myList α → myList α

def empt : myList Nat := myList.nil

def c : myList Nat := myList.cons 3 empt

def removePred (f : Nat -> Bool) (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | x :: xs =>
    if f x then removePred f xs
    else x :: removePred f xs

inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single (a : α) : Palindrome [a]
  | sandwich (a : α) (ev : Palindrome as): Palindrome ([a] ++ as ++ [a])

#check 1 < 2
#check Palindrome [1, 2, 1]

example : Palindrome [1] :=
  Palindrome.single 1

example : 1 < 2 := by
  decide

example : Palindrome [1, 2, 1] :=
  Palindrome.sandwich 1 (Palindrome.single 2)



-- this is autogen code from copilot, it's wrong

theorem all_of_singleton  {P : α → Prop} {a : α} (h : P a) : ∀ x ∈ [a], P x :=
  by
    intros x hx
    simp at hx
    cases hx
    { rw hx, exact h }
    { cases hx }
