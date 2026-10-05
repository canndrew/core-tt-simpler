{-# OPTIONS --rewriting --local-confluence-check --type-in-type --prop #-}

module iso where

open import lib
open import obs

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record Iso (From : Set) (Into : Set) : Set where
    constructor MkIso
    field
        fwd : From -> Into
        rev : Into -> From
        fwd-rev :
            (from : From) ->
            ObsEqual From (rev (fwd from)) from
        rev-fwd :
            (into : Into) ->
            ObsEqual Into (fwd (rev into)) into


dependent-sigma-head-congruence :
    {Head-0 : Set} ->
    {Head-1 : Set} ->
    (head-iso : Iso Head-0 Head-1) ->
    (Tail : (head-0 : Head-0) -> Set) ->
    Iso (Sigma Head-0 Tail) (Sigma Head-1 (\head-1 -> Tail (Iso.rev head-iso head-1)))

dependent-sigma-head-congruence
    {Head-0}
    {Head-1}
    (MkIso head-fwd head-rev head-fwd-rev head-rev-fwd)
    Tail-0
    =
    MkIso fwd rev fwd-rev rev-fwd
    where
        Tail-1 : (head-1 : Head-1) -> Set
        Tail-1 head-1 = Tail-0 (head-rev head-1)

        fwd :
            (sigma-0 : Sigma Head-0 Tail-0) ->
            Sigma Head-1 (\head-1 -> Tail-0 (head-rev head-1))

        fwd (MkSigma head-0 tail-0) =
            let head-1 : Head-1
                head-1 = head-fwd head-0
            in
            let tail-1 : Tail-0 (head-rev head-1)
                tail-1 =
                    (cast
                        (Tail-0 head-0)
                        (Tail-0 (head-rev head-1))
                        (obs-cong
                            (\head-0 -> \_ ->
                                (ObsEqual
                                    Set
                                    (Tail-0 head-0)
                                    (Tail-0 (head-rev head-1))
                                )
                            )
                            (obs-refl (Tail-0 (head-rev head-1)))
                            (head-fwd-rev head-0)
                        )
                        tail-0
                    )
            in
            (MkSigma head-1 tail-1)

        rev :
            (sigma-1 : Sigma Head-1 (\head-1 -> Tail-0 (head-rev head-1))) ->
            Sigma Head-0 Tail-0

        rev (MkSigma head-1 tail) =
            let head-0 : Head-0
                head-0 = head-rev head-1
            in
            (MkSigma head-0 tail)

        fwd-rev :
            (sigma-0 : Sigma Head-0 Tail-0) ->
            ObsEqual
                (Sigma Head-0 Tail-0)
                (rev (fwd sigma-0))
                sigma-0

        fwd-rev (MkSigma head-0 tail-0) =
            let head-1 : Head-1
                head-1 = head-fwd head-0
            in

            let head-eq :
                    (ObsEqual
                        Head-0
                        (head-rev head-1)
                        head-0
                    )
                head-eq = head-fwd-rev head-0
            in

            let BoundTail-0 : Set
                BoundTail-0 = Tail-0 head-0
            in
            let BoundTail-1 : Set
                BoundTail-1 = Tail-1 head-1
            in

            let bound-tail-ty-eq-fwd :
                    (ObsEqual Set BoundTail-0 BoundTail-1)
                bound-tail-ty-eq-fwd =
                    (obs-cong
                        (\head-0 -> \_ ->
                            (ObsEqual
                                Set
                                (Tail-0 head-0)
                                BoundTail-1
                            )
                        )
                        (obs-refl BoundTail-1)
                        head-eq
                    )
            in

            let bound-tail-ty-eq-rev :
                    (ObsEqual Set BoundTail-1 BoundTail-0)
                bound-tail-ty-eq-rev =
                    (obs-cong
                        (\head-0 -> \_ ->
                            (ObsEqual
                                Set
                                BoundTail-1
                                (Tail-0 head-0)
                            )
                        )
                        (obs-refl BoundTail-1)
                        head-eq
                    )
            in

            let tail-1 : BoundTail-1
                tail-1 =
                    (cast
                        BoundTail-0
                        BoundTail-1
                        bound-tail-ty-eq-fwd
                        tail-0
                    )
            in

            let tail-eq :
                    (ObsEqual
                        (Tail-0 head-0)
                        (cast
                            BoundTail-1
                            BoundTail-0
                            bound-tail-ty-eq-rev
                            (cast
                                BoundTail-0
                                BoundTail-1
                                bound-tail-ty-eq-fwd
                                tail-0
                            )
                        )
                        tail-0
                    )
                tail-eq =
                    (cast-round-trip
                        BoundTail-0
                        BoundTail-1
                        bound-tail-ty-eq-fwd
                        bound-tail-ty-eq-rev
                        tail-0
                    )
            in

            (MkPropSigma head-eq tail-eq)


        rev-fwd :
            (sigma-1 : Sigma Head-1 (\head-1 -> Tail-0 (head-rev head-1))) ->
            (ObsEqual
                (Sigma Head-1 (\head-1 -> Tail-0 (head-rev head-1)))
                (fwd (rev sigma-1))
                sigma-1
            )

        rev-fwd (MkSigma head-1 tail-1) =
            let head-0 : Head-0
                head-0 = head-rev head-1
            in
            let head-eq :
                    (ObsEqual
                        Head-1
                        (head-fwd head-0)
                        head-1
                    )
                head-eq = head-rev-fwd head-1
            in

            let BoundTail-0 : Set
                BoundTail-0 = Tail-0 head-0
            in
            let BoundTail-1 : Set
                BoundTail-1 = Tail-1 (head-fwd head-0)
            in

            let bound-tail-ty-eq-fwd :
                    (ObsEqual
                        Set
                        BoundTail-0
                        BoundTail-1
                    )
                bound-tail-ty-eq-fwd =
                    (obs-cong
                        (\head-0 -> \_ ->
                            (ObsEqual
                                Set
                                (Tail-0 head-0)
                                BoundTail-1
                            )
                        )
                        (obs-refl BoundTail-1)
                        (head-fwd-rev head-0)
                    )
            in

            let bound-tail-ty-eq-rev :
                    (ObsEqual
                        Set
                        BoundTail-1
                        BoundTail-0
                    )
                bound-tail-ty-eq-rev =
                    (obs-cong
                        (\head-1 -> \_ ->
                            (ObsEqual
                                Set
                                BoundTail-1
                                (Tail-1 head-1)
                            )
                        )
                        (obs-refl BoundTail-1)
                        head-eq
                    )
            in

            let tail-eq :
                    (ObsEqual
                        BoundTail-0
                        (cast
                            BoundTail-1
                            BoundTail-0
                            bound-tail-ty-eq-rev
                            (cast
                                BoundTail-0
                                BoundTail-1
                                bound-tail-ty-eq-fwd
                                tail-1
                            )
                        )
                        tail-1
                    )
                tail-eq =
                    (cast-round-trip
                        BoundTail-0
                        BoundTail-1
                        bound-tail-ty-eq-fwd
                        bound-tail-ty-eq-rev
                        tail-1
                    )
            in

            (MkPropSigma head-eq tail-eq)


dependent-sigma-tail-congruence :
    (Head : Set) ->
    (Tail-0 : (head : Head) -> Set) ->
    (Tail-1 : (head : Head) -> Set) ->
    (tail-iso : (head : Head) -> Iso (Tail-0 head) (Tail-1 head)) ->
    Iso (Sigma Head Tail-0) (Sigma Head Tail-1)

dependent-sigma-tail-congruence Head Tail-0 Tail-1 tail-iso =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd : 
            (sigma-0 : Sigma Head Tail-0) ->
            (Sigma Head Tail-1)

        fwd (MkSigma head tail-0) =
            (MkSigma
                head
                (Iso.fwd (tail-iso head) tail-0)
            )
    
        rev :
            (sigma-1 : Sigma Head Tail-1) ->
            (Sigma Head Tail-0)

        rev (MkSigma head tail-1) =
            (MkSigma
                head
                (Iso.rev (tail-iso head) tail-1)
            )

        fwd-rev :
            (sigma-0 : Sigma Head Tail-0) ->
            (ObsEqual (Sigma Head Tail-0) (rev (fwd sigma-0)) sigma-0)

        fwd-rev (MkSigma head tail-0) =
            let tail-eq :
                    (ObsEqual
                        (Tail-0 head)
                        (cast
                            (Tail-0 head)
                            (Tail-0 head)
                            (obs-refl (Tail-0 head))
                            (Iso.rev
                                (tail-iso head)
                                (Iso.fwd (tail-iso head) tail-0)
                            )
                        )
                        tail-0
                    )

                tail-eq =
                    (transitivity
                        {Ty = Tail-0 head}
                        {val-0 =
                            (cast
                                (Tail-0 head)
                                (Tail-0 head)
                                (obs-refl (Tail-0 head))
                                (Iso.rev
                                    (tail-iso head)
                                    (Iso.fwd (tail-iso head) tail-0)
                                )
                            )
                        }
                        {val-2 = tail-0}
                        (cast-refl
                            (obs-refl (Tail-0 head))
                            (Iso.rev (tail-iso head) (Iso.fwd (tail-iso head) tail-0))
                        )
                        (Iso.fwd-rev (tail-iso head) tail-0)
                    )
            in

            (MkPropSigma
                (obs-refl head)
                tail-eq
            )

        rev-fwd :
            (sigma-1 : Sigma Head Tail-1) ->
            (ObsEqual (Sigma Head Tail-1) (fwd (rev sigma-1)) sigma-1)

        rev-fwd (MkSigma head tail-1) =
            let tail-eq :
                    (ObsEqual
                        (Tail-1 head)
                        (cast
                            (Tail-1 head)
                            (Tail-1 head)
                            _
                            (Iso.fwd
                                (tail-iso head)
                                (Iso.rev (tail-iso head) tail-1)
                            )
                        )
                        tail-1
                    )
                tail-eq =
                    (transitivity
                        {Ty = Tail-1 head}
                        {val-0 =
                            (cast
                                (Tail-1 head)
                                (Tail-1 head)
                                (obs-refl (Tail-1 head))
                                (Iso.fwd
                                    (tail-iso head)
                                    (Iso.rev (tail-iso head) tail-1)
                                )
                            )
                        }
                        {val-2 = tail-1}
                        (cast-refl
                            (obs-refl (Tail-1 head))
                            (Iso.fwd (tail-iso head) (Iso.rev (tail-iso head) tail-1))
                        )
                        (Iso.rev-fwd (tail-iso head) tail-1)
                    )
            in

            (MkPropSigma
                (obs-refl head)
                tail-eq
            )


sigma-tail-constrains-head :
    (Head : Set) ->
    (Tail : (head : Head) -> Set) ->
    (unique-head : Head) ->
    (constrains : (head : Head) -> (tail : Tail head) -> ObsEqual Head head unique-head) ->
    Iso (Sigma Head Tail) (Tail unique-head)

sigma-tail-constrains-head Head Tail unique-head constrains =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (sigma : Sigma Head Tail) ->
            (Tail unique-head)

        fwd (MkSigma head tail) =
            (cast
                (Tail head)
                (Tail unique-head)
                (congruence Tail (constrains head tail))
                tail
            )

        rev :
            (tail : Tail unique-head) ->
            (Sigma Head Tail)

        rev tail = 
            (MkSigma unique-head tail)

        fwd-rev :
            (sigma : Sigma Head Tail) ->
            ObsEqual (Sigma Head Tail) (rev (fwd sigma)) sigma

        fwd-rev (MkSigma head tail) =
            let tail-eq :
                    (ObsEqual
                        (Tail head)
                        (cast
                            (Tail unique-head)
                            (Tail head)
                            (congruence Tail (symmetry {Ty = Head} (constrains head tail)))
                            (cast
                                (Tail head)
                                (Tail unique-head)
                                (congruence Tail (constrains head tail))
                                tail
                            )
                        )
                        tail
                    )
                tail-eq =
                    (cast-round-trip
                        (Tail head)
                        (Tail unique-head)
                        (congruence Tail (constrains head tail))
                        (congruence Tail (symmetry {Ty = Head} (constrains head tail)))
                        tail
                    )
            in

            (MkPropSigma
                (symmetry {Ty = Head} (constrains head tail))
                tail-eq
            )

        rev-fwd :
            (tail : Tail unique-head) ->
            ObsEqual (Tail unique-head) (fwd (rev tail)) tail

        rev-fwd tail =
            cast-refl (obs-refl (Tail unique-head)) tail


dependent-pi-arg-congruence :
    {Arg-0 : Set} ->
    {Arg-1 : Set} ->
    (arg-iso : Iso Arg-0 Arg-1) ->
    (Res : (arg-0 : Arg-0) -> Set) ->
    Iso ((arg-0 : Arg-0) -> Res arg-0) ((arg-1 : Arg-1) -> Res (Iso.rev arg-iso arg-1))

dependent-pi-arg-congruence {Arg-0} {Arg-1} (MkIso arg-fwd arg-rev arg-fwd-rev arg-rev-fwd) Res =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (func-0 : (arg-0 : Arg-0) -> Res arg-0) ->
            ((arg-1 : Arg-1) -> Res (arg-rev arg-1))
        
        fwd func-0 =
            (\arg-1 ->
                func-0 (arg-rev arg-1)
            )

        rev :
            (func-1 : (arg-1 : Arg-1) -> Res (arg-rev arg-1)) ->
            ((arg-0 : Arg-0) -> Res arg-0)

        rev func-1 =
            (\arg-0 ->
                let arg-0-round-trip : Arg-0
                    arg-0-round-trip = (arg-rev (arg-fwd arg-0))
                in

                (cast
                    (Res arg-0-round-trip)
                    (Res arg-0)
                    (congruence
                        Res
                        {arg-0 = arg-0-round-trip}
                        (arg-fwd-rev arg-0)
                    )
                    (func-1 (arg-fwd arg-0))
                )
            )

        fwd-rev :
            (func-0 : (arg-0 : Arg-0) -> Res arg-0) ->
            ObsEqual ((arg-0 : Arg-0) -> Res arg-0) (rev (fwd func-0)) func-0

        fwd-rev func-0 =
            (\arg-0 ->
                let arg-0-round-trip : Arg-0
                    arg-0-round-trip = arg-rev (arg-fwd arg-0)
                in
                (obs-cong
                    {Ty = Arg-0}
                    (\arg-0 -> \arg-eq ->
                        (ObsEqual
                            (Res arg-0)
                            (cast
                                (Res arg-0-round-trip)
                                (Res arg-0)
                                (congruence
                                    Res
                                    {arg-0 = arg-0-round-trip}
                                    arg-eq
                                )
                                (func-0 arg-0-round-trip)
                            )
                            (func-0 arg-0)
                        )
                    )
                    (cast-refl
                        (obs-refl (Res arg-0-round-trip))
                        (func-0 arg-0-round-trip)
                    )
                    (arg-fwd-rev arg-0)
                )
            )
            
        rev-fwd :
            (func-1 : (arg-1 : Arg-1) -> Res (arg-rev arg-1)) ->
            ObsEqual ((arg-1 : Arg-1) -> Res (arg-rev arg-1)) (fwd (rev func-1)) func-1

        rev-fwd func-1 =
            (\arg-1 ->
                let arg-1-round-trip : Arg-1
                    arg-1-round-trip = arg-fwd (arg-rev arg-1)
                in

                (obs-cong
                    {Ty = Arg-1}
                    (\arg-1 -> \arg-eq ->
                        (ObsEqual
                            (Res (arg-rev arg-1))
                            (cast
                                (Res (arg-rev arg-1-round-trip))
                                (Res (arg-rev arg-1))
                                (congruence
                                    (\arg-1 -> Res (arg-rev arg-1))
                                    {arg-0 = arg-1-round-trip}
                                    arg-eq
                                )
                                (func-1 arg-1-round-trip)
                            )
                            (func-1 arg-1)
                        )
                    )
                    (cast-refl
                        (obs-refl (Res (arg-rev arg-1-round-trip)))
                        (func-1 arg-1-round-trip)
                    )
                    (arg-rev-fwd arg-1)
                )
            )

    
dependent-pi-res-congruence :
    (Arg : Set) ->
    (Res-0 : (arg : Arg) -> Set) ->
    (Res-1 : (arg : Arg) -> Set) ->
    (res-iso : (arg : Arg) -> Iso (Res-0 arg) (Res-1 arg)) ->
    Iso ((arg : Arg) -> Res-0 arg) ((arg : Arg) -> Res-1 arg)

dependent-pi-res-congruence Arg Res-0 Res-1 res-iso =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (func-0 : (arg : Arg) -> Res-0 arg) ->
            ((arg : Arg) -> Res-1 arg)
            
        fwd func-0 =
            (\arg ->
                Iso.fwd (res-iso arg) (func-0 arg)
            )

        rev :
            (func-1 : (arg : Arg) -> Res-1 arg) ->
            ((arg : Arg) -> Res-0 arg)

        rev func-1 =
            (\arg ->
                Iso.rev (res-iso arg) (func-1 arg)
            )
        
        fwd-rev :
            (func-0 : (arg : Arg) -> Res-0 arg) ->
            ObsEqual 
                ((arg : Arg) -> Res-0 arg)
                (rev (fwd func-0))
                func-0

        fwd-rev func-0 =
            (\arg ->
                Iso.fwd-rev (res-iso arg) (func-0 arg)
            )
            
        rev-fwd :
            (func-1 : (arg : Arg) -> Res-1 arg) ->
            ObsEqual
                ((arg : Arg) -> Res-1 arg)
                (fwd (rev func-1))
                func-1

        rev-fwd func-1 =
            (\arg ->
                Iso.rev-fwd (res-iso arg) (func-1 arg)
            )


sigma-sum-head-distribute :
    (Lhs : Set) ->
    (Rhs : Set) ->
    (Tail : (sum : Sum Lhs Rhs) -> Set) ->
    Iso 
        (Sigma (Sum Lhs Rhs) Tail)
        (Sum
            (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
            (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
        )

sigma-sum-head-distribute Lhs Rhs Tail =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd : 
            (sigma : Sigma (Sum Lhs Rhs) Tail) ->
            (Sum
                (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
            )

        fwd (MkSigma sum tail) =
            (case
                (\sum ->
                    (tail : Tail sum) ->
                    (Sum
                        (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                        (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                    )
                )
                (\lhs -> \tail ->
                    (InjLhs (MkSigma lhs tail))
                )
                (\rhs -> \tail ->
                    (InjRhs (MkSigma rhs tail))
                )
                sum
                tail
            )

        rev :
            (sum :
                (Sum
                    (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                    (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                )
            ) -> 
            (Sigma (Sum Lhs Rhs) Tail)

        rev sum =
            (case
                (\_ ->
                    (Sigma (Sum Lhs Rhs) Tail)
                )
                (\(MkSigma lhs tail) -> MkSigma (InjLhs lhs) tail)
                (\(MkSigma rhs tail) -> MkSigma (InjRhs rhs) tail)
                sum
            )

        fwd-rev :
            (sigma : Sigma (Sum Lhs Rhs) Tail) -> 
            ObsEqual
                (Sigma (Sum Lhs Rhs) Tail)
                (rev (fwd sigma))
                sigma

        fwd-rev (MkSigma sum tail) =
            (pcase
                (\sum ->
                    (tail : Tail sum) ->
                    (ObsEqual
                        (Sigma (Sum Lhs Rhs) Tail)
                        (case
                            (\_ ->
                                (Sigma (Sum Lhs Rhs) Tail)
                            )
                            (\(MkSigma lhs tail) -> MkSigma (InjLhs lhs) tail)
                            (\(MkSigma rhs tail) -> MkSigma (InjRhs rhs) tail)
                            (case
                                (\sum ->
                                    (tail : Tail sum) ->
                                    (Sum
                                        (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                                        (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                                    )
                                )
                                (\lhs -> \tail ->
                                    (InjLhs (MkSigma lhs tail))
                                )
                                (\rhs -> \tail ->
                                    (InjRhs (MkSigma rhs tail))
                                )
                                sum
                                tail
                            )
                        )
                        (MkSigma sum tail)
                    )
                )
                (\lhs -> \tail ->
                    obs-refl {Ty = (Sigma (Sum Lhs Rhs) Tail)} (MkSigma (InjLhs lhs) tail)
                )
                (\rhs -> \tail ->
                    obs-refl {Ty = (Sigma (Sum Lhs Rhs) Tail)} (MkSigma (InjRhs rhs) tail)
                )
                sum
                tail
            )

        rev-fwd :
            (sum :
                (Sum
                    (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                    (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                )
            ) -> 
            (ObsEqual
                (Sum
                    (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                    (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                )
                (fwd (rev sum))
                sum
            )

        rev-fwd sum =
            (pcase
                (\sum ->
                    (ObsEqual
                        (Sum
                            (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                            (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                        )
                        (fwd (rev sum))
                        sum
                    )
                )
                (\(MkSigma lhs tail) ->
                    (obs-refl
                        {Ty =
                            (Sum
                                (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                                (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                            )
                        }
                        (InjLhs (MkSigma lhs tail))
                    )
                )
                (\(MkSigma rhs tail) ->
                    (obs-refl
                        {Ty =
                            (Sum
                                (Sigma Lhs (\lhs -> Tail (InjLhs lhs)))
                                (Sigma Rhs (\rhs -> Tail (InjRhs rhs)))
                            )
                        }
                        (InjRhs (MkSigma rhs tail))
                    )
                )
                sum
            )

nat-into-sum-of-zero-and-succs :
    Iso Nat (Sum Unit (Sum Nat Never))

nat-into-sum-of-zero-and-succs = MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (n : Nat) ->
            (Sum Unit (Sum Nat Never))

        fwd n =
            (fold
                (\_ -> Sum Unit (Sum Nat Never))
                (InjLhs MkUnit)
                (\n -> \_ -> InjRhs (InjLhs n))
                n
            )

        rev :
            (sum : Sum Unit (Sum Nat Never)) ->
            Nat

        rev sum =
            (case
                (\_ -> Nat)
                (\_ -> Z)
                (\sum ->
                    (case
                        (\_ -> Nat)
                        (\n -> S n)
                        (\never ->
                            (explode
                                (\_ -> Nat)
                                never
                            )
                        )
                        sum
                    )
                )
                sum
            )

        fwd-rev : 
            (n : Nat) ->
            (ObsEqual Nat (rev (fwd n)) n)

        fwd-rev n =
            (pfold
                (\n ->
                    (ObsEqual Nat (rev (fwd n)) n)
                )
                (obs-refl {Ty = Nat} Z)
                (\n -> \_ ->
                    (obs-refl {Ty = Nat} (S n))
                )
                n
            )

        rev-fwd :
            (sum : Sum Unit (Sum Nat Never)) ->
            (ObsEqual (Sum Unit (Sum Nat Never)) (fwd (rev sum)) sum)

        rev-fwd sum =
            (pcase
                (\sum ->
                    (ObsEqual (Sum Unit (Sum Nat Never)) (fwd (rev sum)) sum)
                )
                (\_ ->
                    (obs-refl {Ty = Sum Unit (Sum Nat Never)} (InjLhs MkUnit))
                )
                (\sum ->
                    (pcase
                        (\sum ->
                            (ObsEqual
                                (Sum Unit (Sum Nat Never))
                                (fwd (rev (InjRhs sum)))
                                (InjRhs sum)
                            )
                        )
                        (\n -> 
                            (obs-refl
                                {Ty = Sum Unit (Sum Nat Never)}
                                (InjRhs (InjLhs n))
                            )
                        )
                        (\never ->
                            (pexplode
                                (\_ ->
                                    (ObsEqual
                                        (Sum Unit (Sum Nat Never))
                                        (fwd (rev (InjRhs (InjRhs never))))
                                        (InjRhs (InjRhs never))
                                    )
                                )
                                never
                            )
                        )
                        sum
                    )
                )
                sum
            )

pi-sigma-res-distribute :
    (Arg : Set) ->
    (Head : (arg : Arg) -> Set) ->
    (Tail : (arg : Arg) -> (head : Head arg) -> Set) ->
    Iso
        ((arg : Arg) -> Sigma (Head arg) (Tail arg))
        (Sigma
            ((arg : Arg) -> Head arg)
            (\head -> (arg : Arg) -> Tail arg (head arg))
        )

pi-sigma-res-distribute Arg Head Tail = MkIso fwd rev fwd-rev rev-fwd
    where

        fwd : 
            (func : (arg : Arg) -> Sigma (Head arg) (Tail arg)) ->
            (Sigma
                ((arg : Arg) -> Head arg)
                (\head -> (arg : Arg) -> Tail arg (head arg))
            )

        fwd func =
            (MkSigma
                (\arg -> Sigma.head (func arg))
                (\arg -> Sigma.tail (func arg))
            )

        rev :
            (sigma : Sigma
                ((arg : Arg) -> Head arg)
                (\head -> (arg : Arg) -> Tail arg (head arg))
            ) ->
            ((arg : Arg) -> Sigma (Head arg) (Tail arg))
        
        rev (MkSigma head tail) =
            (\arg -> MkSigma (head arg) (tail arg))

        fwd-rev :
            (func : (arg : Arg) -> Sigma (Head arg) (Tail arg)) ->
            ObsEqual
                ((arg : Arg) -> Sigma (Head arg) (Tail arg))
                (rev (fwd func))
                func

        fwd-rev func =
            (obs-refl {Ty = ((arg : Arg) -> Sigma (Head arg) (Tail arg))} func)

        rev-fwd :
            (sigma : Sigma
                ((arg : Arg) -> Head arg)
                (\head -> (arg : Arg) -> Tail arg (head arg))
            ) ->
            ObsEqual 
                (Sigma
                    ((arg : Arg) -> Head arg)
                    (\head -> (arg : Arg) -> Tail arg (head arg))
                )
                (fwd (rev sigma))
                sigma

        rev-fwd (MkSigma head tail) =
            (obs-refl
                {Ty = 
                    (Sigma
                        ((arg : Arg) -> Head arg)
                        (\head -> (arg : Arg) -> Tail arg (head arg))
                    )
                }
                (MkSigma head tail)
            )

