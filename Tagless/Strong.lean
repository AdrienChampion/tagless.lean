namespace Ty
  structure Bool : Type u
  structure Nat : Type u
  structure Lst (α : Type u) : Type u
end Ty



namespace Spec
  structure Bool where
    bIdent : Type
    bCst : Type

  structure Nat extends Bool where
    nIdent : Type
    nCst : Type
  
  structure Lst extends Nat where
    lIdent : Type
    lCst (α : Type u) : Type
end Spec



structure BExpr (S : Spec.Bool) where
  R : Type u → Type u
  O : Type u → Type u

  bVar : S.bIdent → R Ty.Bool
  bCst : S.bCst → R Ty.Bool

  conj : Array (R Ty.Bool) → R Ty.Bool
  disj : Array (R Ty.Bool) → R Ty.Bool
  not : R Ty.Bool → R Ty.Bool

  ite : R Ty.Bool → R α → R α → R α
  eq : R α → R α → R Ty.Bool

namespace BExpr
  variable
    {S : Spec.Bool}
    (self : BExpr S)

  def Bool := self.R Ty.Bool
end BExpr



structure NExpr (S : Spec.Nat) extends BExpr S.toBool where
  nVar : S.nIdent → R Ty.Nat
  nCst : S.bCst → R Ty.Nat
  nZero : R Ty.Nat
  nOne : R Ty.Nat

  succ : R Ty.Nat → R Ty.Nat

  nAdd : Array (R Ty.Nat) → R Ty.Nat
  nMul : Array (R Ty.Nat) → R Ty.Nat
  nNeg : R Ty.Nat → R Ty.Nat
  nDiv : R Ty.Nat → R Ty.Nat → R Ty.Nat

  nLt : R Ty.Nat → R Ty.Nat → R Ty.Bool
  nLe : R Ty.Nat → R Ty.Nat → R Ty.Bool

namespace NExpr
  variable
    {S : Spec.Nat}
    (self : NExpr S)

  def Nat := self.R Ty.Nat

  def nIsZero expr :=
    self.eq expr self.nZero
  def nGt lhs rhs :=
    self.nLt lhs rhs
  def nGe lhs rhs :=
    self.nLe lhs rhs
end NExpr



structure LExpr (S : Spec.Lst) extends NExpr S.toNat where
  lVar : S.lIdent → R (Ty.Lst α)
  lCst : S.lCst α → R (Ty.Lst α)

  cons : R α → R (Ty.Lst α) → R (Ty.Lst α)
  app : R (Ty.Lst α) → R (Ty.Lst α) → R (Ty.Lst α)

  len : R (Ty.Lst α) → R Ty.Nat

namespace LExpr
  variable
    {S : Spec.Lst}
    (self : LExpr S)

  def Lst α :=
    Ty.Lst α
    |> self.R

  def lVar' α (id : S.lIdent) : self.R (Ty.Lst α) :=
    self.lVar id
  def lCst' α (cst : S.lCst α) : self.R (Ty.Lst α) :=
    self.lCst cst

  def isEmpty {α} (lst : self.R (Ty.Lst α)) : self.R Ty.Bool :=
    self.len lst
    |> self.nIsZero
end LExpr
