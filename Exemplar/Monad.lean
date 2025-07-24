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

def fprod {α} [Mul α] (x : List α) (y : List α) : List α := do
      pure ((<-x) * (<-y))

def prod {α} [Mul α] (x : List α) (y : List α) : List (List α) := do
  let ax <- x
  pure do
    let ay <- y
    pure (ax * ay)

#eval fprod first second

#eval prod first second

class Zippable (coll: Type -> Type) where
  zip : coll α → coll β → coll (α × β)

def inner [HMul α β γ] [Monad M] [Zippable M] (x : M α) (y : M β) : M γ := do
  let (ax, ay) <- Zippable.zip x y
  pure (ax * ay)

instance : Zippable List where
  zip  := List.zip

#eval inner first second
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
