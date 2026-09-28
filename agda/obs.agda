{-# OPTIONS --rewriting --local-confluence-check --type-in-type --prop #-}

module obs where

open import lib

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
    {-
    IsProp : Set -> Set

    is-prop-set :
        (IsProp Set)
        ≡
        Never

    is-prop-nat :
        (IsProp Nat)
        ≡
        Never

    is-prop-never :
        (IsProp Never)
        ≡
        Unit

    is-prop-unit :
        (IsProp Unit)
        ≡
        Unit

    is-prop-sum :
        (Lhs : Set) ->
        (Rhs : Set) ->
        (IsProp (Sum Lhs Rhs))
        ≡
        Never

    is-prop-sigma :
        (Head : Set) ->
        (Tail : (head : Head) -> Set) ->
        (IsProp (Sigma Head Tail))
        ≡
        (Pair
            (IsProp Head)
            ((head : Head) -> IsProp (Tail head))
        )

    is-prop-pi :
        (Arg : Set) ->
        (Res : (arg : Arg) -> Set) ->
        (IsProp ((arg : Arg) -> Res arg))
        ≡
        ((arg : Arg) -> IsProp (Res arg))
    -}


    ObsEqual :
        (Ty : Set) ->
        (eq-tm-0 : Ty) ->
        (eq-tm-1 : Ty) ->
        Prop

    {-
    is-prop-equal :
        (Ty : Set) ->
        (eq-tm-0 : Ty) ->
        (eq-tm-1 : Ty) ->
        (IsProp (ObsEqual Ty eq-tm-0 eq-tm-1))
        ≡
        Unit
    -}

    obs-refl :
        {Ty : Set} ->
        (eq-tm : Ty) ->
        ObsEqual Ty eq-tm eq-tm

    obs-cong :
        {Ty : Set} ->
        {eq-tm-0 : Ty} ->
        (Motive :
            (eq-tm-1 : Ty) ->
            (elim : ObsEqual Ty eq-tm-0 eq-tm-1) ->
            Prop
        ) ->
        (inhab : Motive eq-tm-0 (obs-refl eq-tm-0)) ->
        {eq-tm-1 : Ty} ->
        (elim : ObsEqual Ty eq-tm-0 eq-tm-1) ->
        Motive eq-tm-1 elim

    cast :
        (From : Set) ->
        (Into : Set) ->
        (tys-eq : ObsEqual Set From Into) ->
        (tm : From) ->
        Into

    cast-refl :
        {Ty : Set} ->
        (ty-eq : ObsEqual Set Ty Ty) ->
        (val : Ty) ->
        (ObsEqual
            Ty
            (cast Ty Ty ty-eq val)
            val
        )


    {-
    obs-equal-unit :
        (eq-tm-0 : Unit) ->
        (eq-tm-1 : Unit) ->
        (ObsEqual Unit eq-tm-0 eq-tm-1)
        ≡
        Unit

    {-# REWRITE obs-equal-unit #-}
    -}

    obs-equal-sum-lhs-lhs :
        {Lhs : Set} ->
        {Rhs : Set} ->
        (lhs-0 : Lhs) ->
        (lhs-1 : Lhs) ->
        (ObsEqual (Sum Lhs Rhs) (InjLhs lhs-0) (InjLhs lhs-1))
        ≡
        (ObsEqual Lhs lhs-0 lhs-1)
        
    obs-equal-sum-lhs-rhs :
        {Lhs : Set} ->
        {Rhs : Set} ->
        (lhs-0 : Lhs) ->
        (rhs-1 : Rhs) ->
        (ObsEqual (Sum Lhs Rhs) (InjLhs lhs-0) (InjRhs rhs-1))
        ≡
        PropNever

    obs-equal-sum-rhs-lhs :
        {Lhs : Set} ->
        {Rhs : Set} ->
        (rhs-0 : Rhs) ->
        (lhs-1 : Lhs) ->
        (ObsEqual (Sum Lhs Rhs) (InjRhs rhs-0) (InjLhs lhs-1))
        ≡
        PropNever
        
    obs-equal-sum-rhs-rhs :
        {Lhs : Set} ->
        {Rhs : Set} ->
        (rhs-0 : Rhs) ->
        (rhs-1 : Rhs) ->
        (ObsEqual (Sum Lhs Rhs) (InjRhs rhs-0) (InjRhs rhs-1))
        ≡
        (ObsEqual Rhs rhs-0 rhs-1)

    {-# REWRITE
        obs-equal-sum-lhs-lhs
        obs-equal-sum-lhs-rhs
        obs-equal-sum-rhs-lhs
        obs-equal-sum-rhs-rhs
    #-}

    obs-equal-sigma :
        {Head : Set} ->
        {Tail : (head : Head) -> Set} ->
        (eq-tm-0 : Sigma Head Tail) ->
        (eq-tm-1 : Sigma Head Tail) ->
        (ObsEqual (Sigma Head Tail) eq-tm-0 eq-tm-1)
        ≡
        (PropSigma
            (ObsEqual Head (Sigma.head eq-tm-0) (Sigma.head eq-tm-1))
            (\head-eq ->
                (ObsEqual
                    (Tail (Sigma.head eq-tm-1))
                    (cast
                        (Tail (Sigma.head eq-tm-0))
                        (Tail (Sigma.head eq-tm-1))
                        (obs-cong
                            (\head-tm-1 -> \_ ->
                                (ObsEqual Set (Tail (Sigma.head eq-tm-0)) (Tail head-tm-1))
                            )
                            (obs-refl (Tail (Sigma.head eq-tm-0)))
                            head-eq
                        )
                        (Sigma.tail eq-tm-0)
                    )
                    (Sigma.tail eq-tm-1)
                )
            )
        )

    {-# REWRITE obs-equal-sigma #-}

    obs-equal-pi :
        {Arg : Set}
        {Res : (arg : Arg) -> Set} ->
        (func-0 : (arg : Arg) -> Res arg) ->
        (func-1 : (arg : Arg) -> Res arg) ->
        (ObsEqual ((arg : Arg) -> Res arg) func-0 func-1)
        ≡
        ((arg : Arg) -> (ObsEqual (Res arg) (func-0 arg) (func-1 arg)))

    {-# REWRITE obs-equal-pi #-}


symmetry :
    {Ty : Set} ->
    {val-0 : Ty} ->
    {val-1 : Ty} ->
    (val-eq : ObsEqual Ty val-0 val-1) ->
    ObsEqual Ty val-1 val-0
symmetry {Ty} {val-0} val-eq =
    (obs-cong
        (\val-1 -> \_ -> ObsEqual Ty val-1 val-0)
        (obs-refl val-0)
        val-eq
    )


transitivity :
    {Ty : Set} ->
    {val-0 : Ty} ->
    {val-1 : Ty} ->
    {val-2 : Ty} ->
    (eq-0 : ObsEqual Ty val-0 val-1) ->
    (eq-1 : ObsEqual Ty val-1 val-2) ->
    ObsEqual Ty val-0 val-2
transitivity {Ty} {val-0} {val-1} {val-2} eq-0 eq-1 =
    (obs-cong
        (\val-1 -> \_ ->
            (eq-1 : ObsEqual Ty val-1 val-2) ->
            ObsEqual Ty val-0 val-2
        )
        (\eq-1 -> eq-1)
        eq-0
        eq-1
    )

congruence :
    {Arg : Set} ->
    {Res : Set} ->
    (func : Arg -> Res) ->
    {arg-0 : Arg} ->
    {arg-1 : Arg} ->
    (arg-eq : ObsEqual Arg arg-0 arg-1) ->
    ObsEqual Res (func arg-0) (func arg-1)
congruence {Arg} {Res} func {arg-0} arg-eq =
    (obs-cong
        (\arg-1 -> \_ ->
            ObsEqual Res (func arg-0) (func arg-1)
        )
        (obs-refl (func arg-0))
        arg-eq
    )

cast-round-trip :
    (From : Set) ->
    (Into : Set) ->
    (eq-0 : ObsEqual Set From Into) ->
    (eq-1 : ObsEqual Set Into From) ->
    (val : From) ->
    (ObsEqual
        From
        (cast Into From eq-1 (cast From Into eq-0 val))
        val
    )

cast-round-trip From Into eq-0 eq-1 val =
    (obs-cong
        (\Into -> \eq-0 ->
            (eq-1 : ObsEqual Set Into From) ->
            (ObsEqual
                From
                (cast Into From eq-1 (cast From Into eq-0 val))
                val
            )
        )
        (\eq-1 ->
            (transitivity
                {Ty = From}
                {val-0 = cast From From eq-1 (cast From From (obs-refl From) val)}
                {val-1 = cast From From (obs-refl From) val}
                {val-2 = val}
                (cast-refl
                    eq-1
                    (cast From From (obs-refl From) val)
                )
                (cast-refl
                    (obs-refl From)
                    val
                )
            )
        )
        eq-0
        eq-1
    )


