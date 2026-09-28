{-# OPTIONS --rewriting --type-in-type --prop #-}

module lib where

data Never : Set where

data PropNever : Prop where

record Unit : Set where
    constructor MkUnit
    eta-equality

data Sum (Lhs : Set) (Rhs : Set) : Set where
    InjLhs :
        (lhs : Lhs) -> Sum Lhs Rhs
    InjRhs :
        (rhs : Rhs) -> Sum Lhs Rhs

record PropSigma
        (Head : Prop)
        (Tail : (head : Head) -> Prop) :
        Prop where
    constructor MkPropSigma
    field
        head : Head
        tail : Tail head

record Sigma
        (Head : Set)
        (Tail : (head : Head) -> Set) :
        Set where
    constructor MkSigma
    eta-equality
    field
        head : Head
        tail : Tail head

record PropPair
        (Head : Prop)
        (Tail : Prop) :
        Prop where
    constructor MkPair
    field
        head : Head
        tail : Tail

record Pair
        (Head : Set)
        (Tail : Set) :
        Set where
    constructor MkPair
    eta-equality
    field
        head : Head
        tail : Tail

data Nat : Set where
    Z : Nat
    S : Nat -> Nat

postulate
    Name : Set

explode :
    (Motive : (elim : Never) -> Set) ->
    (elim : Never) ->
    Motive elim
explode Motive ()

pexplode :
    (Motive : (elim : Never) -> Prop) ->
    (elim : Never) ->
    Motive elim
pexplode Motive ()

case :
    {Lhs : Set} ->
    {Rhs : Set} ->
    (Motive : (elim : Sum Lhs Rhs) -> Set) ->
    (lhs-inhab : (lhs : Lhs) -> Motive (InjLhs lhs)) ->
    (rhs-inhab : (rhs : Rhs) -> Motive (InjRhs rhs)) ->
    (elim : Sum Lhs Rhs) ->
    Motive elim
case Motive lhs-inhab rhs-inhab (InjLhs lhs) =
    lhs-inhab lhs
case Motive lhs-inhab rhs-inhab (InjRhs rhs) =
    rhs-inhab rhs

pcase :
    {Lhs : Set} ->
    {Rhs : Set} ->
    (Motive : (elim : Sum Lhs Rhs) -> Prop) ->
    (lhs-inhab : (lhs : Lhs) -> Motive (InjLhs lhs)) ->
    (rhs-inhab : (rhs : Rhs) -> Motive (InjRhs rhs)) ->
    (elim : Sum Lhs Rhs) ->
    Motive elim
pcase Motive lhs-inhab rhs-inhab (InjLhs lhs) =
    lhs-inhab lhs
pcase Motive lhs-inhab rhs-inhab (InjRhs rhs) =
    rhs-inhab rhs

fold :
    (Motive : (elim : Nat) -> Set) ->
    (zero-inhab : Motive Z) ->
    (succ-inhab :
        (elim : Nat) ->
        (state : Motive elim) ->
        Motive (S elim)
    ) ->
    (elim : Nat) ->
    Motive elim
fold Motive zero-inhab succ-inhab Z =
    zero-inhab
fold Motive zero-inhab succ-inhab (S elim) =
    succ-inhab elim (fold Motive zero-inhab succ-inhab elim)

pfold :
    (Motive : (elim : Nat) -> Prop) ->
    (zero-inhab : Motive Z) ->
    (succ-inhab :
        (elim : Nat) ->
        (state : Motive elim) ->
        Motive (S elim)
    ) ->
    (elim : Nat) ->
    Motive elim
pfold Motive zero-inhab succ-inhab Z =
    zero-inhab
pfold Motive zero-inhab succ-inhab (S elim) =
    succ-inhab elim (pfold Motive zero-inhab succ-inhab elim)

