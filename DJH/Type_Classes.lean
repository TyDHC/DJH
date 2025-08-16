import Mathlib.Tactic


-- #min_imports
#version

-- Type classes were introduced as a principled way of enabling ad-hoc polymorphism in functional programming languages.
-- Type Classes
namespace Type_Classes

structure Add (α : Type) where
  add : α → α → α   -- 相当于一个函数

#print Add.add
#check @Add.add

-- We could implement double by:
def double {α : Type} (s : Add α) (x : α) : α :=
  s.add x x

#eval double {add := Nat.add} 10   -- 20
#eval double {add := Nat.mul} 10   -- 100
#eval double {add := Int.add} 10   -- 20


/-
The main idea behind type classes is to make arguments such as Add a implicit,
and to use a database of user-defined instances to synthesize the desired instances automatically through a process known as typeclass resolution.

In Lean, by changing structure to class in the example above, the type of Add.add becomes:
-/
namespace structure_changeto_class

class Add (a : Type) where
  add : a → a → a

#check @Add.add
-- @Add.add : {a : Type} → [self : Add a] → a → a → a
-- the square brackets indicate that the argument of type Add a is instance implicit

-- Similarly, we can register instances by:
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

/-
Then for n : Nat and m : Nat, the term Add.add n m triggers typeclass resolution with the goal of
Add Nat,
and typeclass resolution will synthesize the instance for Nat above.
We can now reimplement double using an instance implicit by:
-/
def double {a : Type} [Add a] (x : a) : a :=
  Add.add x x

#check @double
#print double

#eval double 10
#eval double (10 : Int)
#eval double (7 : Float)
#eval double (239.1 + 2)

/-
In general, instances may depend on other instances in complicated ways.
For example, you can declare an (anonymous) instance stating that if a has addition,
then Array a has addition:
-/
instance {a : Type} [Add a] : Add (Array a) where
  add x y := Array.zipWith (fun x y => Add.add x y) x y

#print Add.add
/-
def Type_Classes.structure_changeto_class.Add.add : {a : Type} → [self : Add a] → a → a → a :=
fun a [self : Add a] => self.1
-/

#print instAddArray
/-
def Type_Classes.structure_changeto_class.instAddArray : {a : Type} → [Add a] → Add (Array a) :=
fun {a} [Add a] => { add := fun x y => Array.zipWith (fun x y => Add.add x y) x y }
-/

#eval Add.add #[1, 2, 3] #[4, 5, 6] -- #[5, 7, 9]

end structure_changeto_class


/-
The standard library defines a type class Inhabited to enable type class inference to infer a
"default" element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:
-/
universe u
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- @Inhabited.default : {a : Type u_1} → [self : Inhabited a] → a
#print default

-- Now we populate the class with some instances:
instance : Inhabited Bool where
  default := true

instance : Inhabited ℕ where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : ℕ)    -- 0
#eval (Inhabited.default : Bool) -- true

-- You can use the command export to create the alias default for Inhabited.default
export Inhabited (default)

#eval (default : ℕ)    -- 0
#eval (default : Bool) -- true

end Type_Classes






-- Chaining Instances
namespace Chaining_Instances

/-
What makes type class inference powerful is that one can chain instances.
That is, an instance declaration can in turn depend on an implicit instance of a type class.
-/

-- For example, the following definition shows that if two types a and b are inhabited, then so is
-- their product:
instance {a b : Type} [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

/-
With this added to the earlier instance declarations, type class instance can infer,
for example, a default element of Nat × Bool:
-/
namespace Ex
universe u
variable (a b : Type u)

class Inhabited (a : Type u) where
  default : a

instance :Inhabited Bool where
  default := true
instance :Inhabited ℕ where
  default := 0

opaque default [Inhabited a] : a :=
  Inhabited.default

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : ℕ × Bool) -- (0, true)

-- Similarly, we can inhabit type function with suitable constant functions:
instance {α β : Type u} [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default

end Ex


namespace inferInstance_example
/-
The Lean standard library contains the definition inferInstance.
It has type {α : Sort u} → [i : α] → α,
and is useful for triggering the type class resolution procedure when the expected type is an
instance.
-/
#check (inferInstance : Inhabited ℕ)

#print inferInstance
-- @[reducible] def inferInstance.{u} : {α : Sort u} → [i : α] → α := fun {α} [i : α] => i

def foo : Inhabited (ℕ × ℕ) :=
  inferInstance

theorem ex : foo.default = (default, default) := by
  rfl


end inferInstance_example

end Chaining_Instances






-- ToString
namespace ToString_example

/-The polymorphic method toString has type {α : Type u} → [ToString α] → α → String. -/
structure Person where
  name : String
  age  : ℕ

#print Person

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString {name := "Leo", age := 542 : Person}
#eval toString ({name := "Leo", age := 542 : Person}, "hello")

end ToString_example







-- Numerals
namespace Numerals_example

/-Numerals are polymorphic in Lean-/
structure Rational where
  num : ℤ
  den : ℕ
  inv : den ≠ 0


/-
The OfNat instance is parametric on the numeral. So, you can define instances for particular
numerals.
The second argument is often a variable as in the example above, or a raw natural number.
-/
variable {n : ℕ}
instance : OfNat Rational n where
  ofNat := {num := n, den := 1, inv := by decide}

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)  -- 2/1
#check (2 : Rational) -- 2 : Rational
#check (2 : ℕ) -- 2 : ℕ

#print OfNat
/-
class OfNat.{u} (α : Type u) : ℕ → Type u
number of parameters: 2
fields:
  OfNat.ofNat : α
constructor:
  OfNat.mk.{u} {α : Type u} {x✝ : ℕ} (ofNat : α) : OfNat α x✝
-/
universe u
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance {α : Type} [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

#eval nat_lit 1

def getUnit {α : Type} [Monoid α] : α :=
  1


end Numerals_example







-- Output Parameters
namespace Output_Parameters

/-In the following example,
we use output parameters to define a heterogeneous polymorphic multiplication.-/
universe u v w
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)


#eval hMul 2 3 -- 6
#eval hMul 2 #[1, 2, 3] -- #[2, 4, 6]

/-
The parameters α and β are considered input parameters and γ an output one.

In the example above, we defined two instances.
The first one is the homogeneous multiplication for natural numbers.
The second is the scalar multiplication for arrays.
-/


instance : HMul ℤ ℤ ℤ where
  hMul := Int.mul

instance {α β γ : Type} [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 2 3 -- 6
#eval hMul 2 #[1, 2, 3] -- #[2, 4, 6]
#eval hMul (-2) #[3, -1, 3] -- #[-6, 2, -6]
#eval hMul 2 #[#[1, 2], #[3, 4]] -- #[#[2, 4], #[6, 8]]

#help tactic map

end Output_Parameters







-- Default Instances
namespace Default_Instances

universe u v w

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

/-
instance : HMul ℤ ℤ ℤ where
  hMul := Int.mul

def xs : List ℤ := [1, 2, 3]

#check_failure fun y => xs.map (fun x => hMul x y)

typeclass instance problem is stuck, it is often due to metavariables
  HMul ℤ ?m.33414 (?m.33445 y)
-/

@[default_instance]
instance : HMul ℤ ℤ ℤ where
  hMul := Int.mul

def xs : List ℤ := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)


/-
The instance OfNat Nat n is the default instance (with priority 100) for the OfNat class. This is
why the numeral 2 has type Nat when the expected type is not known. You can define default instances
with higher priority to override the builtin ones.
-/
structure Rational where
  num : ℤ
  den : ℕ
  inv : den ≠ 0

variable {n : ℕ}

@[default_instance 101]
instance : OfNat Rational n where
  ofNat := {num := n, den := 1, inv := by decide}

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- 2 : Rational




/-
Priorities are also useful to control the interaction between different default instances.

以下这个例子没有看懂
-/
namespace Ex
-- Ex is shorthand for example
class OfNat_Ex (α : Type u) (n : ℕ) where
  ofNat_Ex : α

@[default_instance]
instance (n : ℕ) : OfNat_Ex Nat n where
  ofNat_Ex := n

class HMul_Ex (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul_Ex : α → β → γ

class Mul_Ex (α : Type u) where
  mul_Ex : α → α → α

@[default_instance 10]
instance {α : Type} [Mul_Ex α] : HMul_Ex α α α where
  hMul_Ex a b := Mul_Ex.mul_Ex a b

infixl : 70 " * " => HMul_Ex.hMul_Ex

end Ex


end Default_Instances










--Loacal Instances
namespace Local_Instances

/-
Type classes are implemented using attributes in Lean.
Thus, you can use the local modifier to indicate that they only have effect until the
current section or namespace is closed, or until the end of the current file.
-/
structure Point where
  x : ℤ
  y : ℤ

section

local instance : Add Point where
  add p1 p2 := {x := p1.x + p2.x, y := p1.y + p2.y}

def double (p : Point) : Point :=
  p + p

end   -- instance `Add Point` is not active anymore

/-
You can also temporarily disable an instance using the attribute command until the current section
or namespace is closed, or until the end of the current file.

for example, the following command disables the instance Add Point:
add `attribute [-instance] addPoint`, remove `local`
-/

-- We recommend you only use this command to diagnose problems.

end Local_Instances








-- Scoped Instances
namespace Scoped_Instances

/-
You can also declare scoped instances in namespaces.
This kind of instance is only active when you are inside of the namespace or open the namespace.
-/
structure Point where
  x : ℤ
  y : ℤ

namespace Point

scoped instance : Add Point where
  add p1 p2 := {x := p1.x + p2.x, y := p1.y + p2.y}

def double (p : Point) : Point :=
  p + p

end Point
-- instance `Add Point` is not active anymore
-- #check fun (p : Point) => p + p + p   -- Error


namespace Point
#check fun (p : Point) => p + p   -- fun p ↦ p + p : Point → Point
end Point

section t1
open Point
#check fun (p : Point) => p + p
#check fun (p : Point) => double p   -- fun p ↦ p + p + p : Point → Point
end t1

-- #check fun (p : Point) => p + p   -- error

section t2
/-
You can use the command open scoped <namespace> to activate scoped attributes
but will not "open" the names from the namespace.
-/
open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p
-- #check fun (p : Point) => double p -- `Error`: unknown identifier 'double'
-- end
end t2

end Scoped_Instances











-- Decidable Propositions
namespace Decidable_Propositions

/-
Roughly speaking, an element of Prop is said to be decidable if we can decide whether it is true or false.
The distinction is only useful in constructive mathematics; classically, every proposition is decidable.

But if we use the classical principle, say, to define a function by cases,
that function will not be computable.
-/

-- In the standard library, Decidable is defined formally as follows:
class inductive Decidable (p : Prop) where
  | isFalse : ¬p → Decidable p
  | isTrue  : p → Decidable p

universe u

def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

/-
The standard library also contains a variant of ite called dite, the dependent if-then-else
expression.
It is defined as follows:
-/
def dite (α : Sort u) (c : Prop) [h : Decidable c] (t : c → α) (e : ¬c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t


/-
Without classical logic, we cannot prove that every proposition is decidable.
But we can prove that certain propositions are decidable.

For example, we can prove the decidability of basic operations like equality and comparisons on the
natural numbers and the integers.
Moreover, decidability is preserved under propositional connectives:
-/
#check @instDecidableAnd
-- ⊢ {p q : Prop} → [dp : _root_.Decidable p] → [dq : _root_.Decidable q] → _root_.Decidable (p ∧ q)

#check @instDecidableOr

#check @instDecidableNot



-- Thus we can carry out definitions by cases on decidable predicates on the natural numbers:
def step (a b x : ℕ) : ℕ :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
/-
def Decidable_Propositions.step : Nat → Nat → Nat → Nat :=
fun a b x ↦
  @_root_.ite Nat (Or (@LT.lt Nat instLTNat x a) (@GT.gt Nat instLTNat x b))
    (@instDecidableOr (@LT.lt Nat instLTNat x a) (@GT.gt Nat instLTNat x b) (x.decLt a) (b.decLt x))
    (@OfNat.ofNat Nat 0 (instOfNatNat 0)) (@OfNat.ofNat Nat 1 (instOfNatNat 1))
-/
set_option pp.explicit false



/-
With the classical axioms, we can prove that every proposition is decidable.
-/
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩


/-
The Decidable type class also provides a bit of small-scale automation for proving theorems.
The standard library introduces the tactic decide that uses the Decidable instance to solve simple
goals.
-/
example : 10 < 5 ∨ 1 > 0 := by
  hint

example : ¬ (True ∧ False) := by
  decide

theorem ex : True ∧ 2 = 1 + 1 := by
  decide

end Decidable_Propositions













-- Managing Type Class Inference
namespace Managing_Type_Class_Inference

def foo : Add ℕ := inferInstance
def bar : Inhabited (ℕ → ℕ) := inferInstance

#check inferInstance

#check (inferInstance : Add ℕ)

#check (inferInstance : Inhabited (ℕ → ℕ))



/-
Sometimes Lean can't find an instance because the class is buried under a definition.
For example, Lean cannot find an instance of Inhabited (Set α). We can declare one explicitly:
-/
universe u

def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance {α : Type} : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))



/-
You can change the order that type class instances are tried by assigning them a priority.
When an instance is declared, it is assigned a default priority value.
You can assign other priorities when defining an instance.
-/
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 2

instance i2 : Foo where
  a := 3
  b := 4

example : Foo.a = 1 :=
  rfl

instance (priority := default + 2) i3 : Foo where
  a := 5
  b := 6

example : Foo.a = 5 :=
  rfl

end Managing_Type_Class_Inference






-- Coercions using Type Classes
namespace Coercions_using_Type_Classes

/-
The most basic type of coercion maps elements of one type to another.
For example, a coercion from Nat to Int allows us to view any element n : Nat as an element of Int.

But some coercions depend on parameters;
for example, for any type α, we can view any element as : List α as an element of Set α,
namely, the set of elements occurring in the list.

The corresponding coercion is defined on the "family" of types List α, parameterized by α.


Lean allows us to declare three kinds of coercions:

  from a family of types to another family of types
  from a family of types to the class of sorts
  from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family.
The second kind of coercion allows us to view any element of a member of the source family as a type.
The third kind of coercion allows us to view any element of the source family as a function.

-/
instance : Coe Bool Prop where
  coe b := b = true

#eval if true then 5 else 3
#eval if false then 5 else 3


-- We can define a coercion from List α to Set α as follows:
-- 总有错！！！
universe u
variable {α : Type u}
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x

notation "{ " a " }" => Set.singleton a
infix : 55 " ∪ " => Set.union

def List.toSet : List α → Set α
  | [] => Set.empty
  | a::as => {a} ∪ as.toSet


instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set ℕ := {1}
#check s ∪ [2, 3]





end Coercions_using_Type_Classes
