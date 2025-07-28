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

#eval first.foldl Add.add 0 -- already defined for list

-- we define for a general forable object

class Foldable (M : Type → Type) β where
  foldl :  (α → β → α ) -> α -> ( M β) -> α

instance {M : Type → Type} [ForIn Id (M β) β] : Foldable M β where
  foldl {α}  (op : (α → β → α )) (init : α ) (xs: M β ) : α  := Id.run do
    let mut a := init
    for x in xs do
      a := op a x
    return a

#eval Foldable.foldl Add.add 0 first

#eval Foldable.foldl (fun l e => List.cons e l) [] first

--- turning any iterable into a list ---

class ToList (M : Type -> Type) α where
  toList : (M α ) -> List α

instance {M : Type -> Type} [ForIn Id (M α) α]  : ToList M α where
  toList (xs: M α) : List α := Foldable.foldl (fun l e => l ++ [e]) [] xs

instance [ToList M α] : CoeOut (M α) (List α) where
  coe := ToList.toList

#eval ToList.toList first

--- Zipping  ----

class Zippable (M N : Type → Type) α β where
  zipWith : (α -> β -> γ) -> (M α) → (N β) → List γ
  zip : (M α) → (N β) → List (α × β) := zipWith Prod.mk

instance [ToList M α] [ToList N β]: Zippable M N α β  where
  zipWith {γ} (op : (α -> β -> γ)) (x: (M α)) (y: (N β) ) :  List γ :=
    List.zipWith op x y -- uses coercion to list

#eval Zippable.zip first second

def elmul  {M N : Type → Type} [HMul α β γ] [Zippable M N α β]  : M α -> N β -> List γ := Zippable.zipWith HMul.hMul

#eval elmul first second

-- Inner products --

def genInner {M : Type → Type} {N: Type -> Type } [Zippable M N α β] (op2 :  δ -> γ → δ ) (init: δ) (op1 : α -> β -> γ) (xs : M α) (ys : N β) : δ :=
  Foldable.foldl op2 init (Zippable.zipWith op1 xs ys)

def inner : List Int -> List Int -> Int := genInner Add.add 0 Mul.mul

#eval inner first second

-- examples of some unsafe coercions

instance [Monad M]: Coe α (M α) where
  coe := pure

#check ( (· + 1) : List (Nat->Nat))

def x :=  1

#eval ( x: List Nat)
#eval ( x: Option Nat)
#eval ( x: Except String Nat)

instance [Monad M]: OfNat (M Nat) n where
  ofNat := (n: M Nat)

#eval ( 1: List Nat)
