import ai_podt


section Chap1

#check Vector
#check Vector.toArray
#check Vector.size

-- Parameters vs indices?
inductive myvec a : Nat -> Type where
  | mynil : myvec a 0
 -- recusion is on second argument in addition. How could I have known that?
 -- | mycons : a -> myvec a n -> myvec a (1 + n)
  | mycons : a -> myvec a n -> myvec a (n + 1)

#print Nat.add

def myhead {n : Nat} : myvec a n.succ -> a
| .mycons x _ => x

def mytail {n : Nat} : myvec a n.succ -> myvec a n
| .mycons _ tl => tl


-- THis version accidentally has the right recursion
def myapp {n m : Nat} : myvec a n -> myvec a m -> myvec a (m + n)
| .mycons x tl, y => .mycons x (myapp tl y)
|  .mynil , y => y

-- Why was this accepted if it works by recursio nover second argument?
-- What are the different ways of writing this to add enoguh proof ?
def myapp2 {n m : Nat} : myvec a n -> myvec a m -> myvec a (n + m)
-- Can I use exact + grind ? Is cast (by grind) a common pattern?
| .mycons x tl, y => cast (by grind) (myvec.mycons x (myapp2 tl y))
| .mynil , y => cast (by grind) y
#check Vector.cast
-- This version is too cute by half. I don't understand ▸
--| .mycons x tl, y => Nat.succ_add _ _ ▸ .mycons x (myapp2 tl y)
--| .mynil , y => (Nat.zero_add _).symm ▸ y
--| .mycons x tl, y => .mycons x (myapp2 tl y)
--|  .mynil , y => y

-- #check Vector.filter Not a thing
#check List.filter
#check Array.filter

example (l : List A) f : (l.filter f).length <= l.length := by
  -- show_term apply? exact? simp? grind?
  exact List.length_filter_le f l -- ctrl+.
  --exact List.length_filter_le f l -- Is there a hotkey to auto past the result of exact?

-- what is show_term for?
end Chap1



section Chap2

-- Is there a shorter syntax for simple inductives? Or do I jave to do : ty -> ty -> ty
inductive ty where
  | base
  | arr (a b : ty)
  | tup (a b : ty)
deriving Repr, DecidableEq

inductive tyjudge : ty -> Prop  where
  | base : tyjudge .base
  | arr : tyjudge a -> tyjudge b -> tyjudge (.arr a b)
  | tup : tyjudge a -> tyjudge b -> tyjudge (.tup a b)

/-
instance : DecidablePred tyjudge
| .base => .base
| .arr a b =>  .arr (decide) (decide)
| .tup a b => .tup (decide) (decide)
-/

#check isTrue
instance : DecidablePred tyjudge := by
  intro t
  refine (isTrue ?_)
  induction t <;> constructor <;> assumption

-- siggestions ? alternatives ?


end Chap2
