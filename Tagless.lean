import Tagless.Tests
import Tagless.Strong


structure Dsl where
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



def Dsl.example
  (dsl : Dsl)
: dsl.Repr Nat :=
  let v1 := dsl.val 7
  let v2 := dsl.val 3
  let f := dsl.val fun l r => l + r
  let tmp := dsl.app f v1
  dsl.app tmp v2




def Dsl.eval : Dsl where
  Repr := id
  Obsv := id

  observe := id

  val := id
  app f a := f a

#eval Dsl.example Dsl.eval

