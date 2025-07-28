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

def moprod [Applicative m] (op : α -> β -> γ) (x : m α) (y: m β) : m γ :=
  (pure op) <*> x <*> y

def fpprod [Monad m] (op : α -> β -> γ) (x: m α) (y: m β) : m γ := do
  pure (op (← x) (← y))

def mpprod [Monad m] (op : α -> β -> γ) (x: m α) (y: m β) : m (m γ) := do
  let ax <- x
  pure do
    let ay <- y
    pure (op ax ay)

def mmprod [HMul α β γ] [Applicative m] : m α -> m β -> m γ := moprod HMul.hMul

#eval fpprod (· * ·) first second

#eval mpprod (· * ·) first second

#eval mpprod (·.toString ++ ·.toString) "Hello".toList "World".toList

#eval mmprod first second

---- reductions ----

def reduce {M : Type → Type} [ForIn Id (M α) α] (op: α → β → β ) (init: β) (xs: M α) : β := Id.run do
  let mut a := init
  for x in xs do
    a := op x a
  return a

#eval reduce Add.add 0 first

#eval reduce List.cons [] first

--- Zipping and Inner Products ----

def toList {M : Type → Type} [ForIn Id (M α) α] (xs: M α) : List α := reduce List.cons [] xs

#eval toList first

class Zippable (M N : Type → Type) α β where
  zip : (M α) → (N β) → List (α × β)
  zipWith : (α -> β -> γ) -> (M α) → (N β) → List γ :=
    fun op xs ys => do
      let (x, y) <- zip xs ys
      pure (op x y)

instance {M N : Type → Type} [ForIn Id (M α) α] [ForIn Id (N β ) β]: Zippable M N α β  where
  zip (x: (M α)) (y: (N β) ) :  List (α × β)  :=
    List.zip (toList x) (toList y)

#eval Zippable.zip first second

def elmul  {M N : Type → Type} [HMul α β γ] [Zippable M N α β]  : M α -> N β -> List γ :=
  Zippable.zipWith HMul.hMul

#eval elmul first second

def genInner {M : Type → Type} {N: Type -> Type } [Zippable M N α β] (op2 : γ → δ → δ ) (init: δ): (α -> β -> γ) -> (M α) -> (N β) -> δ :=
  fun op1 xs ys => reduce op2 init (Zippable.zipWith op1 xs ys)

def inner : List Int -> List Int -> Int := genInner Add.add 0 Mul.mul

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
