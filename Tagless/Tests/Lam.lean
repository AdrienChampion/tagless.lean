structure Lam where
  Repr : Type v → Type v
  Obsv : Type v → Type v

  observe
    {α : Type v}
  : Repr α → Obsv α

  val
    {α : Type v}
  : α → Repr α

  app
    {α β : Type v}
  : Repr (α → β) → Repr α → Repr β



def Lam.example
  (dsl : Lam)
: dsl.Repr Nat :=
  let v1 := dsl.val 7
  let v2 := dsl.val 3
  let f := dsl.val fun l r => l + r
  let tmp := dsl.app f v1
  dsl.app tmp v2




def Lam.eval : Lam where
  Repr := id
  Obsv := id

  observe := id

  val := id
  app f a := f a

#eval Lam.example Lam.eval

