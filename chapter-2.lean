set_option diagnostics true
set_option diagnostics.threshold 33

namespace AAAAAA
  /- Define some constants. -/
  def m : Nat := 1
  def n : Nat := 0
  def b1 : Bool := true
  def b2 : Bool := false

  /- Check their types. -/
  #check m
  #check n
  #check n + 1
  #check m * (n + 1)
  #check b1
  #check b1 && b2
  #check b1 || b2
  #check true

  /- Evaluate -/
  #eval 5 * 4
  #eval m + 2
  #eval b1 && b2
end AAAAAA

namespace AAAAAA.mine
  #check true
  #check false
  #check Bool

  #check True
  #check False
  #check bool

  -- #check 1 + true
  -- #eval 1 + true
end AAAAAA.mine

namespace AAABBB
  #check Nat → Nat
  #check Nat -> Nat

  #check Nat × Nat
  #check Prod Nat Nat

  #check Nat → Nat → Nat
  #check Nat → (Nat → Nat)

  #check Nat × Nat → Nat
  #check (Nat → Nat) → Nat

  #check Nat.succ
  #check (0, 1)
  #check Nat.add

  #check Nat.succ 2
  #check Nat.add 3
  #check Nat.add 5 2
  #check (5, 9).1
  #check (5, 9).2

  #eval Nat.succ 2
  #eval Nat.add 5 2
  #eval (5, 9).1
  #eval (5, 9).2
end AAABBB

namespace AAABBB.mine
  #check (Nat × Nat) → Nat
  #check Nat × (Nat → Nat)

  #check (Nat.succ)

  -- #eval Nat.add 3

  def m : Nat := 1000
  def n : Nat := 2000
  #check (m, n)

  def p : Nat × Nat := (m, n)
  #check p.1
  #check p.2
end AAABBB.mine

namespace AAACCC
  #check Nat
  #check Bool
  #check Nat → Bool
  #check Nat × Bool
  #check Nat → Nat
  #check Nat × Nat → Nat
  #check Nat → Nat → Nat
  #check Nat → (Nat → Nat)
  #check Nat → Nat → Bool
  #check (Nat → Nat) → Nat
end AAACCC

namespace AAADDD
  def α : Type := Nat
  def β : Type := Bool
  def F : Type → Type := List
  def G : Type → Type → Type := Prod

  #check α
  #check F α
  #check F Nat
  #check G α
  #check G α β
  #check G α Nat

  -- #eval α
end AAADDD

namespace AAAEEE
  def α : Type := Nat
  def β : Type := Bool

  #check Prod α β
  #check α × β

  #check Prod Nat Nat
  #check Nat × Nat
end AAAEEE

namespace AAAFFF
  def α : Type := Nat

  #check List α
  #check List Nat
end AAAFFF

namespace AAAGGG
  #check Type
end AAAGGG

namespace AAAHHH
  #check Type
  #check Type 1
  #check Type 2
  #check Type 3
  #check Type 4
end AAAHHH

namespace AAAIII
  #check Type
  #check Type 0
end AAAIII

namespace AAAIII.mine
  #check trivial
  #check True
  #check Prop
  #check Sort 0

  #check true
  #check Bool
  #check Type
  #check Sort 1

  #check fun n => Fin n
  #check Nat -> Type
  #check Type 1
  #check Sort 2

  #check fun(_ : Type) => Type
  #check Type -> Type 1
  #check Type 2
  #check Sort 3
end AAAIII.mine

namespace AAAJJJ
  #check List
  #check (List)
end AAAJJJ

namespace AAAKKK
  #check Prod
  #check (Prod)
end AAAKKK

namespace AAALLL
  universe u

  def F (α : Type u) : Type u := Prod α α

  #check F
  #check (F)

  -- #check u
  #check Type u
end AAALLL

namespace AAAMMM
  def F.{u} (α : Type u) : Type u := Prod α α

  #check F
  #check (F)
end AAAMMM

namespace AAANNN
  #check fun (x : Nat) => x + 5
  #check λ (x : Nat) => x + 5
  #check fun x => x + 5
  #check λ x => x + 5
end AAANNN

namespace AAAOOO
  #eval (λ x : Nat => x + 5) 10
end AAAOOO

namespace AAAPPP
  #check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
  #check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
  #check fun x y => if not y then x + 1 else x + 2
end AAAPPP

namespace AAAQQQ
  set_option linter.unusedVariables false

  def f (n : Nat) : String := toString n
  def g (s : String) : Bool := s.length > 0

  #check fun x : Nat => x
  #check fun x : Nat => true
  #check fun x : Nat => g (f x)
  #check fun x => g (f x)
end AAAQQQ

namespace AAARRR
  #check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
end AAARRR

namespace AAARRR.mine
  #check λ
    (g : String → Bool)
    (f : Nat → String)
    (x : Nat)
  =>
    g (f x)

  #check (
    λ g f x => g (f x)
      : (String → Bool) → (Nat → String) → Nat → Bool
  )
end AAARRR.mine

namespace AAASSS
  #check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
end AAASSS

namespace AAATTT
  set_option linter.unusedVariables false

  #check (fun x : Nat => x) 1
  #check (fun x : Nat => true) 1

  def f (n : Nat) : String := toString n
  def g (s : String) : Bool := s.length > 0

  #check
    (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x))
    Nat String Bool g f 0
end AAATTT

namespace AAAUUU
  set_option linter.unusedVariables false

  #eval (fun x : Nat => x) 1
  #eval (fun x : Nat => true) 1
end AAAUUU

namespace AAAVVV
  def double (x : Nat) : Nat := x + x
end AAAVVV

namespace AAAWWW
  def double (x : Nat) : Nat := x + x

  #eval double 3
end AAAWWW

namespace AAAXXX
  def double : Nat → Nat := fun x => x + x

  #eval double 3
end AAAXXX

namespace AAAYYY
  def double := fun (x : Nat) => x + x
end AAAYYY

namespace AAAZZZ
  def pi := 3.141592654
end AAAZZZ

namespace BBBAAA
  def double := fun (x : Nat) => x + x

  def add (x : Nat) (y : Nat) := x + y

  #eval add (double 3) (7 + 9)
end BBBAAA

namespace BBBBBB
  def greater (x y : Nat) :=
    if x > y
    then x
    else y

  #eval greater 1 2
  #eval greater 2 1
end BBBBBB

namespace BBBCCC
  def double := fun (x : Nat) => x + x

  def doTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

  #eval doTwice double 2
  #eval doTwice double (double (double (double (double 2))))
end BBBCCC

namespace BBBDDD
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)
end BBBDDD

namespace BBBEEE
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
   g (f x)
  def double (x : Nat) : Nat := x + x
  def square (x : Nat) : Nat := x * x

  #eval compose Nat Nat Nat double square 3
end BBBEEE

namespace BBBFFF
  #check let y := 2 + 2; y * y
  #eval let y := 2 + 2; y * y

  def twice_double (x : Nat) : Nat :=
    let y := x + x; y * y

  #eval twice_double 2
end BBBFFF

namespace BBBFFF.mine
  -- let x = 1 + 1

  def twice_double : Nat → Nat := λ x =>
    let y := x + x
    y * y

  #check twice_double

  #eval twice_double 2

  #check (
    let y := 2 + 2
    y * y
  )
end BBBFFF.mine

namespace BBBGGG
  #check let y := 2 + 2; let z := y + y; z * z
  #eval let y := 2 + 2; let z := y + y; z * z
end BBBGGG

namespace BBBHHH
  def t (x : Nat) : Nat :=
    let y := x + x
    y * y
end BBBHHH

namespace BBBIII
  def foo := let a := Nat; fun x : a => x + 2

  -- def bar := (fun a => fun x : a => x + 2) Nat
  -- def bar := fun a => fun x : a => x + 2
  -- def bar := (fun a : Type => fun x : a => x + 2) Nat
  -- def bar := fun a : Type => fun x : a => x + 2
  -- def bar := fun (a : Type) (x : a) => x + 2
  -- def bar (a : Type) (x : a) := x + 2
  -- def bar (a : Type) (x : a) : Nat := x + 2
end BBBIII

namespace BBBJJJ
  def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  def doTwice (α : Type) (h : α → α) (x : α) : α :=
    h (h x)

  def doThrice (α : Type) (h : α → α) (x : α) : α :=
    h (h (h x))
end BBBJJJ

namespace BBBKKK
  variable (α β γ : Type)

  def compose (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

  def doTwice (h : α → α) (x : α) : α :=
    h (h x)

  def doThrice (h : α → α) (x : α) : α :=
    h (h (h x))
end BBBKKK

namespace BBBLLL
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #print compose
  #print doTwice
  #print doThrice
end BBBLLL

namespace BBBLLL.mine
  section
    variable (α β γ : Type)
    variable (g : β → γ) (f : α → β) (h : α → α)
    variable (x : α)
    def compose := g (f x)
  end

  #check compose
end BBBLLL.mine

namespace BBBMMM
  section useful
    variable (α β γ : Type)
    variable (g : β → γ) (f : α → β) (h : α → α)
    variable (x : α)

    def compose := g (f x)
    def doTwice := h (h x)
    def doThrice := h (h (h x))
  end useful
end BBBMMM

namespace BBBMMM.mine
  section
    variable
      (α β γ : Type)
      (g : β → γ)
      (f : α → β)
      (h : α → α)
      (x : α)

    def compose := g (f x)
    def doTwice := h (h x)
  end

  section variable
    (α β γ : Type)
    (h : α → α)
    (x : α)
    def doThrice := h (h (h x))
  end

  #check doThrice
  #check (doThrice)
  #print doThrice
end BBBMMM.mine

namespace BBBNNN
  namespace Foo
    def a : Nat := 5
    def f (x : Nat) : Nat := x + 7

    def fa : Nat := f a
    def ffa : Nat := f (f a)

    #check a
    #check f
    #check (f)
    #check fa
    #check ffa
    #check Foo.fa
  end Foo

  -- #check a
  -- #check f
  #check Foo.a
  #check Foo.f
  #check Foo.fa
  #check Foo.ffa

  open Foo

  #check a
  #check f
  #check fa
  #check Foo.ffa
end BBBNNN

namespace BBBNNN.mine
  section open BBBNNN.Foo
    #check a
    #check f
    #check fa
    #check ffa
  end

  -- #check a
  -- #check f
  -- #check fa
  -- #check ffa
end BBBNNN.mine

namespace BBBOOO
  #check List.nil
  #check List.cons
  #check List.map
end BBBOOO

namespace BBBPPP
  open List
  #check nil
  #check cons
  #check map
end BBBPPP

namespace BBBQQQ
  namespace Foo
    def a : Nat := 5
    def f (x: Nat) : Nat := x + 7

    def fa : Nat := f a

    namespace Bar
      def ffa : Nat := f (f a)

      #check fa
      #check Bar.ffa
    end Bar
  end Foo

  #check Foo.fa
  #check Foo.Bar.ffa

  open Foo

  #check fa
  #check Bar.ffa
  -- #check ffa
end BBBQQQ

namespace BBBRRR
  namespace Foo
    def a : Nat := 5
    def f (x : Nat) : Nat := x + 7

    def fa : Nat := f a
  end Foo

  #check Foo.a
  #check Foo.f

  namespace Foo
    def ffa : Nat := f (f a)
  end Foo
end BBBRRR

namespace BBBSSS
  def cons (α : Type) (a : α) (as : List α) : List α :=
    List.cons a as

  #check cons Nat
  #check cons Bool
  #check cons
  #check (cons)
end BBBSSS

namespace BBBTTT
  #check @List.cons
  #check @List.nil
  #check @List.length
  #check @List.append
end BBBTTT

namespace BBBTTT.mine
  #check (List.cons)
  #check @List.cons
  #check (List.nil)
  #check @List.nil
  #check (List.length)
  #check @List.length
  #check (List.append)
  #check @List.append
end BBBTTT.mine

namespace BBBUUU
  universe u v

  def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a
    := ⟨a, b⟩

  def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a
    := Sigma.mk a b

  def h1 (x : Nat) : Nat :=
    (f Type (fun α => α) Nat x).2

  #eval h1 5

  def h2 (x : Nat) : Nat :=
    (g Type (fun α => α) Nat x).2

  #eval h2 5
end BBBUUU

namespace BBBVVV
  universe u

  def Lst (α : Type u) : Type u :=
    List α
  def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α :=
    List.cons a as
  def Lst.nil (α : Type u) : Lst α :=
    List.nil
  def Lst.append (α : Type u) (as bs : Lst α) : Lst α :=
    List.append as bs

  #check Lst
  #check Lst.cons
  #check Lst.nil
  #check Lst.append
end BBBVVV

namespace BBBWWW
  open BBBVVV

  #check Lst.cons Nat 0 (Lst.nil Nat)

  def as : Lst Nat := Lst.nil Nat
  def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

  #check Lst.append Nat as bs
end BBBWWW

namespace BBBXXX
  open BBBVVV

  #check Lst.cons _ 0 (Lst.nil _)

  def as : Lst Nat := Lst.nil _
  def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

  #check Lst.append _ as bs
end BBBXXX

namespace BBBXXX.mine
  open BBBVVV

  #check Lst.cons _ 0 (Lst.nil _)

  def as := Lst.nil Nat
  def bs := Lst.cons _ 5 (Lst.nil _)

  #check Lst.append _ as bs
end BBBXXX.mine

namespace BBBYYY
  universe u

  def Lst (α : Type u) : Type u := List α

  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α :=
    List.cons a as
  def Lst.nil {α : Type u} : Lst α :=
    List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α :=
    List.append as bs

  #check Lst.cons 0 Lst.nil

  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil

  #check Lst.append as bs
end BBBYYY

namespace BBBYYY.mine
  def Lst.{u} : (α : Type u) → Type u :=
    λ α ↦ List α

  def Lst.cons.{u} : {α : Type u} → α → Lst α → Lst α :=
    λ a as ↦ List.cons a as

  def Lst.nil.{u} : {α : Type u} → Lst α :=
    List.nil

  def Lst.append.{u} : {α : Type u} → Lst α → Lst α → Lst α :=
    λ as bs ↦ List.append as bs

  #check Lst.cons 0 Lst.nil

  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil

  #check Lst.append as bs
end BBBYYY.mine

namespace BBBZZZ
  universe u

  def ident {α : Type u} (x : α) := x

  #check ident
  #check (ident)
  #check ident 1
  #check ident "hello"
  #check @ident
end BBBZZZ

namespace BBBZZZ.mine
  def decltype.{u} : {α : Type u} → α → Type u :=
    λ {α} _ ↦ α

  -- universe u
  -- def decltype {α : Type u} (_ : α) := α

  #check decltype
  #check (decltype)
  #check @decltype
  #print decltype

  #check decltype 1
  -- #eval decltype 1

  -- #eval Nat = Nat
end BBBZZZ.mine

namespace CCCAAA
  universe u

  section
    variable {a : Type u}
    variable (x : α)
    def ident := x
  end

  #check ident
  #check ident 4
  #check ident "hello"
end CCCAAA

namespace CCCBBB
  #check List.nil
  #check id

  #check (List.nil : List Nat)
  #check (id : Nat → Nat)
end CCCBBB

namespace CCCBBB.mine
  #check List Type
  #check List Prop
  -- #check List True
  -- #check List trivial
  #check List Bool
  -- #check List true
end CCCBBB.mine

namespace CCCCCC
  #check 2
  #check (2 : Nat)
  #check (2 : Int)
end CCCCCC

namespace CCCDDD
  #check @id
  #check @id Nat
  #check @id Bool

  #check @id Nat 1
  #check @id Bool true
end CCCDDD
