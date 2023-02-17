structure Arith (α : Type u) where
  R : Type u → Type u
  O : Type u → Type u

  lit : α → R α
  add : R α → R α → R α
  mul : R α → R α → R α

  observe : R α → O α

instance instCoeFunArithObserve
: CoeFun (Arith α) (fun A => A.R α → A.O α) where
  coe A := A.observe

def Arith.run
  (A : Arith α)
  (r : A.R α)
: A.O α :=
  A.observe r

def Arith.test1 : {A : Arith Nat} → A.R Nat
| ⟨_, _, lit, add, mul, _⟩ =>
  mul (add (lit 1) (lit 2)) (add (lit 3) (lit 4))

def Arith.test2 : {A : Arith Nat} → A.R Nat
| ⟨_, _, lit, add, mul, _⟩ =>
  let i := lit 1
  let n := lit 2
  let s := lit 3
  let j := lit 10
  let h := lit 100

  let ji := add i j
  let hji := add ji h
  let r := mul n s

  mul r hji

protected abbrev Arith.eval
  [A : HAdd α α α]
  [M : HMul α α α]
: Arith α :=
  ⟨id, id, id, A.hAdd, M.hMul, id⟩

protected abbrev Arith.toString
  [ToString α]
: Arith α where
  R _ := Nat → String
  O _ := String
  lit n _ := toString n
  add l r d :=
    s!"{l 3} + {r 4}"
    |> parenIf (d > 3)
  mul l r d :=
    s!"{l 4} * {r 5}"
    |> parenIf (d > 4)
  observe r :=
    r 0
where
  paren s :=
    s!"({s})"
  parenIf (b : Bool) :=
    if b then paren else id
  

#eval Arith.eval Arith.test1
-- 21
#eval Arith.toString Arith.test1
-- "(1 + 2) * (3 + 4)"

#eval Arith.eval Arith.test2
-- 666
#eval Arith.toString Arith.test2
-- "2 * 3 * (1 + 10 + 100)"



class BoolLike (α : Type u) where
  boolify : α → Bool
  unBoolify : Bool → α

instance instBoolLikeBool : BoolLike Bool :=
  ⟨id, id⟩



structure BArith
  (α : Type u)
  (β : Type u)
extends
  Arith α
where
  bLit : β → R β
  ite : R β → (Unit → R γ) → (Unit → R γ) → R γ
  eql [BEq γ] : R γ → R γ → R β
  lt [lt : LT γ] [DecidableRel lt.lt] : R γ → R γ → R β

instance instCoeFunBArithObserve
: CoeFun (BArith α β) (fun A => A.R α → A.O α) where
  coe A := A.observe

def BArith.test1 {A : outParam <| BArith Nat Bool} : A.R Nat :=
  let a1 := fun _ => @Arith.test1 A.toArith
  let a2 := fun _ => @Arith.test2 A.toArith
  A.ite (A.bLit false) a1 a2

def BArith.eval
  [A : HAdd α α α]
  [M : HMul α α α]
  [B : BoolLike β]
: BArith α β where
  toArith := Arith.eval
  bLit := id

  ite (cnd : β) thn els :=
    if B.boolify cnd then thn () else els ()

  eql
    {γ : Type} [beq : BEq γ]
    l r
  :=
    beq.beq l r |> B.unBoolify

  lt
    {γ : Type} [lt : LT γ] [dec : DecidableRel lt.lt]
    l r
  :=
    dec l r |>.decide |> B.unBoolify


protected def BArith.toString
  [ToString α]
  [ToString β]
: BArith α β where
  toArith := Arith.toString
  bLit b _ := toString b

  ite cnd thn els p :=
    s! "if {cnd 0} then {thn () 0} else {els () 0}"
    |> Arith.toString.parenIf (p > 0)

  eql l r p :=
    s! "{l 1} = {r 1}"
    |> Arith.toString.parenIf (p > 0)
  
  lt l r p :=
    s! "{l 1} < {r 1}"
    |> Arith.toString.parenIf (p > 0)

#eval BArith.eval BArith.test1
-- 666
#eval BArith.toString BArith.test1
-- "if false then (1 + 2) * (3 + 4) else 2 * 3 * (1 + 10 + 100)"