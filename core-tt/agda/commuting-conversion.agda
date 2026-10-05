{-# OPTIONS --rewriting --type-in-type --prop #-}

module commuting-conversion where

open import Agda.Builtin.Equality
open import lib
open import obs

postulate

    explode-through-app :
        (Arg : Set) ->
        (Res : (arg : Arg) -> Set) ->
        (elim : Never) ->
        (arg : Arg) ->
        (explode
            (\_ -> (arg : Arg) -> Res arg)
            elim
            arg
        )
        ≡
        (explode
            (\_ -> Res arg)
            elim
        )

    case-through-app :
        (Lhs : Set) ->
        (Rhs : Set) ->
        (Arg : Set) ->
        (Res : (arg : Arg) -> Set) ->
        (elim : Sum Lhs Rhs) ->
        (lhs-inhab : (lhs : Lhs) -> (arg : Arg) -> Res arg) ->
        (rhs-inhab : (rhs : Rhs) -> (arg : Arg) -> Res arg) ->
        (arg : Arg) ->
        (case
            {Lhs}
            {Rhs}
            (\_ -> (arg : Arg) -> Res arg)
            lhs-inhab
            rhs-inhab
            elim
            arg
        )
        ≡
        (case
            {Lhs}
            {Rhs}
            (\_ -> Res arg)
            (\lhs -> lhs-inhab lhs arg)
            (\rhs -> rhs-inhab rhs arg)
            elim
        )

    explode-through-explode :
        (Motive : (elim : Never) -> Set) ->
        (elim : Never) ->
        (explode
            Motive
            (explode
                (\_ -> Never)
                elim
            )
        )
        ≡
        (explode
            (\elim ->
                (Motive 
                    (explode
                        (\_ -> Never)
                        elim
                    )
                )
            )
            elim
        )

    case-through-explode :
        (Lhs : Set) ->
        (Rhs : Set) ->
        (Motive : (elim : Never) -> Set) ->
        (lhs-inhab : (lhs : Lhs) -> Never) ->
        (rhs-inhab : (rhs : Rhs) -> Never) ->
        (elim : Sum Lhs Rhs) ->
        (explode
            Motive
            (case
                (\_ -> Never)
                lhs-inhab
                rhs-inhab
                elim
            )
        )
        ≡
        (case
            (\elim ->
                (Motive
                    (case
                        (\_ -> Never)
                        lhs-inhab
                        rhs-inhab
                        elim
                    )
                )
            )
            (\lhs ->
                (explode
                    Motive
                    (lhs-inhab lhs)
                )
            )
            (\rhs ->
                (explode
                    Motive
                    (rhs-inhab rhs)
                )
            )
            elim
        )
        

    explode-through-case :
        (Lhs : Set) ->
        (Rhs : Set) ->
        (Motive : (sum : Sum Lhs Rhs) -> Set) ->
        (elim : Never) ->
        (lhs-inhab : (lhs : Lhs) -> Motive (InjLhs lhs)) ->
        (rhs-inhab : (rhs : Rhs) -> Motive (InjRhs rhs)) ->
        (case
            Motive
            lhs-inhab
            rhs-inhab
            (explode
                (\_ -> Sum Lhs Rhs)
                elim
            )
        )
        ≡
        (explode
            (\elim ->
                (Motive
                    (explode
                        (\_ -> Sum Lhs Rhs)
                        elim
                    )
                )
            )
            elim
        )

    case-through-case :
        (Lhs0 : Set) ->
        (Rhs0 : Set) ->
        (Lhs1 : Set) ->
        (Rhs1 : Set) ->
        (Motive : (sum : Sum Lhs1 Rhs1) -> Set) ->
        (lhs-inhab-0 : (lhs : Lhs0) -> Sum Lhs1 Rhs1) ->
        (rhs-inhab-0 : (rhs : Rhs0) -> Sum Lhs1 Rhs1) ->
        (lhs-inhab-1 : (lhs : Lhs1) -> Motive (InjLhs lhs)) ->
        (rhs-inhab-1 : (rhs : Rhs1) -> Motive (InjRhs rhs)) ->
        (elim : Sum Lhs0 Rhs0) ->
        (case
            Motive
            lhs-inhab-1
            rhs-inhab-1
            (case
                (\_ -> Sum Lhs1 Rhs1)
                lhs-inhab-0
                rhs-inhab-0
                elim
            )
        )
        ≡
        (case
            (\elim ->
                (Motive
                    (case
                        (\_ -> Sum Lhs1 Rhs1)
                        lhs-inhab-0
                        rhs-inhab-0
                        elim
                    )
                )
            )
            (\lhs ->
                (case
                    Motive
                    lhs-inhab-1
                    rhs-inhab-1
                    (lhs-inhab-0 lhs)
                )
            )
            (\rhs ->
                (case
                    Motive
                    lhs-inhab-1
                    rhs-inhab-1
                    (rhs-inhab-0 rhs)
                )
            )
            elim
        )



    case-through-app-more-dep :
        (Lhs : Set) ->
        (Rhs : Set) ->
        (Arg : Set) ->
        (Res : (elim : Sum Lhs Rhs) -> (arg : Arg) -> Set) ->
        (elim : Sum Lhs Rhs) ->
        (lhs-inhab : (lhs : Lhs) -> (arg : Arg) -> Res (InjLhs lhs) arg) ->
        (rhs-inhab : (rhs : Rhs) -> (arg : Arg) -> Res (InjRhs rhs) arg) ->
        (arg : Arg) ->
        (case
            {Lhs}
            {Rhs}
            (\elim -> (arg : Arg) -> Res elim arg)
            lhs-inhab
            rhs-inhab
            elim
            arg
        )
        ≡
        (case
            {Lhs}
            {Rhs}
            (\elim -> Res elim arg)
            (\lhs -> lhs-inhab lhs arg)
            (\rhs -> rhs-inhab rhs arg)
            elim
        )

