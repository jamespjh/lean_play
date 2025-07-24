import Mathlib.Data.List.Basic
import Std.Data.Iterators.Producers
import Std.Data.Iterators.Combinators.Zip

def mktwo (a:Nat) (b:Nat) : List Nat := [a, b ]

def double (a:Nat) : Nat := a + a

def first := [1, 2, 3]
def second := [4, 5, 6]

#eval (· , ·) 1 2

#eval [mktwo] <*> first <*> first
#eval [([· , ·])] <*> first <*> second

#check [mktwo]

#eval [double] <*> first  -- [2, 4, 6]

def fpo := do
  pure (1 + (<-first))

def fprod [Mul α] (x : List α) (y : List α) : List α := do
      pure ((<-x) * (<-y))

def prod [Mul α] (x : List α) (y : List α) : List (List α) := do
  let ax <- x
  pure do
    let ay <- y
    pure (ax * ay)

def mfprod [HMul α β γ] [Monad m] (x: m α) (y: m β) : m γ := do
  pure ((<-x) * (<-y))

def xlprod [Mul α] (x : List α) (y : List α) : List α :=
  ([(· * ·)] <*> x <*> y)

def fmprod [HMul α β γ] [Monad m] (x : m α) (y: m β) : m γ :=
  pure (· * ·) <*> x <*> y

def mprod [HMul α β γ] [Monad m] (x : m α) (y: m β) : m (m γ) := do
  let ax <- x
  pure do
    let ay <- y
    pure (ax * ay)

def fpprod [Monad m] (op : α -> β -> γ) (x: m α) (y: m β) : m γ := do
  pure (op (← x) (← y))

def mpprod [Monad m] (op : α -> β -> γ) (x: m α) (y: m β) : m (m γ) := do
  let ax <- x
  pure do
    let ay <- y
    pure (op ax ay)



#eval fprod first second

#eval prod first second

#eval fmprod first second

#eval mfprod first second

#eval fpprod (· * ·) first second

#eval mpprod (· * ·) first second

#eval mpprod (·.toString ++ ·.toString) "Hello".toList "World".toList

class Zippable (coll: Type -> Type) where
  zip : coll α → coll β → coll (α × β)

def inner [HMul α β γ] [Monad M] [Zippable M] (x : M α) (y : M β) : M γ := do
  let (ax, ay) <- Zippable.zip x y
  pure (ax * ay)

def pinner [Monad M] [Zippable M] (op : α -> β -> γ) (x : M α) (y : M β) : M γ := do
  let (ax, ay) <- Zippable.zip x y
  pure (op ax ay)

instance : Zippable List where
  zip  := List.zip

#eval inner first second

#eval pinner Mul.mul first second

---- reductions ----

def reduce [Zero β] [Monad M] [ForIn Id (M α) α] (op: β → α → β ) (xs: M α) : β := Id.run do
  let mut a := (0: β)
  for x in xs do
    a := op a x
  return a

def fred  [Zero β] [Monad M] (op: β → α → β ) (xs: M α) : β :=
  -- make a state monad with int as a transformed version of M



#eval reduce Add.add first

-- examples of some unsafe coercions

instance [Monad M]: Coe α (M α) where
  coe α := pure α

#check ( (· + 1) : List (Nat->Nat))

def x :=  1

#eval ( x: List Nat)
#eval ( x: Option Nat)
#eval ( x: Except String Nat)

instance [Monad M]: OfNat (M Nat) n where
  ofNat := (n: M Nat)

#eval ( 1: List Nat)
