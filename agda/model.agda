{-# OPTIONS --rewriting --type-in-type --prop #-}

module model where

open import lib
open import iso
open import obs

data Mtype (Ctx : Set) : Set

Decode : {Ctx : Set} -> Mtype Ctx -> (ctx : Ctx) -> Set

data Mtype Ctx where
    mtype-subst :
        {Origin : Set} ->
        (subst : Ctx -> Origin) ->
        (ty : Mtype Origin) ->
        Mtype Ctx
    mtype-unit :
        Mtype Ctx
    mtype-sigma :
        (head-ty : Mtype Ctx) ->
        (tail-ty : Mtype (Sigma Ctx (Decode head-ty))) ->
        Mtype Ctx
    mtype-pi :
        (arg-ty : Mtype Ctx) ->
        (res-ty : Mtype (Sigma Ctx (Decode arg-ty))) ->
        Mtype Ctx

Decode (mtype-subst subst ty) ctx =
    Decode ty (subst ctx)

Decode mtype-unit ctx =
    Unit

Decode (mtype-sigma head-ty tail-ty) ctx =
    (Sigma
        (Decode head-ty ctx)
        (\head -> Decode tail-ty (MkSigma ctx head))
    )

Decode (mtype-pi arg-ty res-ty) ctx =
    (arg : (Decode arg-ty ctx)) ->
    (Decode res-ty (MkSigma ctx arg))


subst-weaken :
    {Ctx : Set} ->
    (var-ty : Mtype Ctx) ->
    (Sigma Ctx (Decode var-ty)) ->
    Ctx

subst-weaken var-ty (MkSigma ctx _) = ctx

subst-lift :
    {Origin : Set} ->
    {Target : Set} ->
    (subst : Target -> Origin) ->
    (var-ty : Mtype Origin) ->
    (Sigma Target (\ctx -> Decode var-ty (subst ctx))) ->
    Sigma Origin (Decode var-ty)

subst-lift {Origin} {Target} subst var-ty (MkSigma target ty) =
    MkSigma (subst target) ty

subst-cons :
    {Ctx : Set} ->
    (ty : Mtype Ctx) ->
    (tm : (ctx : Ctx) -> Decode ty ctx) ->
    Ctx ->
    (Sigma Ctx (Decode ty))
subst-cons ty tm ctx = (MkSigma ctx (tm ctx))

subst-append :
    {Origin : Set} ->
    {Middle : Set} ->
    {Target : Set} ->
    (subst-0 : Middle -> Origin) ->
    (subst-1 : Target -> Middle) ->
    Target ->
    Origin
subst-append subst-0 subst-1 target = subst-0 (subst-1 target)


distribute-pi-over-sigmas-mtype :
    {Ctx : Set} ->
    (arg-ty : Mtype Ctx) ->
    (res-ty : Mtype (Sigma Ctx (Decode arg-ty))) ->
    Mtype Ctx

distribute-pi-over-sigmas-mtype {Ctx} arg-ty mtype-unit =
    mtype-unit

distribute-pi-over-sigmas-mtype {Ctx} arg-ty (mtype-sigma head-ty tail-ty) =
    let new-head-ty : Mtype Ctx
        new-head-ty = mtype-pi arg-ty head-ty
    in
    let new-tail-ty : Mtype (Sigma Ctx (Decode new-head-ty))
        new-tail-ty =
                (mtype-pi
                    (mtype-subst
                        (subst-weaken new-head-ty)
                        arg-ty
                    )
                    (mtype-subst
                        (\(MkSigma (MkSigma ctx head) arg) ->
                            (MkSigma (MkSigma ctx arg) (head arg))
                        )
                        tail-ty
                    )
                )
    in
    (mtype-sigma new-head-ty new-tail-ty)
    
distribute-pi-over-sigmas-mtype {Ctx} arg-ty res-ty =
    mtype-pi arg-ty res-ty


distribute-pi-over-sigmas-iso :
    {Ctx : Set} ->
    (arg-ty : Mtype Ctx) ->
    (res-ty : Mtype (Sigma Ctx (Decode arg-ty))) ->
    (ctx : Ctx) ->
    (Iso
        (Decode (mtype-pi arg-ty res-ty) ctx)
        (Decode (distribute-pi-over-sigmas-mtype arg-ty res-ty) ctx)
    )

distribute-pi-over-sigmas-iso arg-ty mtype-unit ctx =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (input : (Decode (mtype-pi arg-ty mtype-unit) ctx)) ->
            Unit
            
        fwd input = MkUnit

        rev :
            (output : Unit) ->
            (Decode (mtype-pi arg-ty mtype-unit) ctx)
        rev MkUnit arg = MkUnit

        fwd-rev :
            (input : (Decode (mtype-pi arg-ty mtype-unit) ctx)) ->
            ObsEqual
                ((Decode (mtype-pi arg-ty mtype-unit) ctx))
                (rev (fwd input))
                input

        fwd-rev input arg = obs-refl {Ty = Unit} MkUnit

        rev-fwd :
            (output : Unit) ->
            ObsEqual
                (Decode (distribute-pi-over-sigmas-mtype arg-ty mtype-unit) ctx)
                (fwd (rev output))
                output

        rev-fwd MkUnit = obs-refl {Ty = Unit} MkUnit

distribute-pi-over-sigmas-iso {Ctx} arg-ty (mtype-sigma head-ty tail-ty) ctx =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (input :
                (arg : (Decode arg-ty ctx)) ->
                (Decode (mtype-sigma head-ty tail-ty) (MkSigma ctx arg))
            ) ->
            (Sigma
                (
                    (arg : (Decode arg-ty ctx)) ->
                    (Decode head-ty (MkSigma ctx arg))
                )
                (\head ->
                    (Decode
                        (mtype-pi
                            (mtype-subst
                                (subst-weaken
                                    (mtype-pi arg-ty head-ty)
                                )
                                arg-ty
                            )
                            (mtype-subst
                                (\(MkSigma (MkSigma ctx head) arg) ->
                                    (MkSigma (MkSigma ctx arg) (head arg))
                                )
                                tail-ty
                            )
                        )
                        (MkSigma ctx head)
                    )
                )
            )
            
        fwd = ?

        rev :
            (output : Decode (distribute-pi-over-sigmas-mtype arg-ty (mtype-sigma head-ty tail-ty)) ctx) ->
            (Decode (mtype-pi arg-ty (mtype-sigma head-ty tail-ty)) ctx)
        rev = ?

        fwd-rev :
            (input : (Decode (mtype-pi arg-ty (mtype-sigma head-ty tail-ty)) ctx)) ->
            ObsEqual
                ((Decode (mtype-pi arg-ty (mtype-sigma head-ty tail-ty)) ctx))
                (rev (fwd input))
                input

        fwd-rev = ?

        rev-fwd :
            (output : Decode (distribute-pi-over-sigmas-mtype arg-ty (mtype-sigma head-ty tail-ty)) ctx) ->
            ObsEqual
                (Decode (distribute-pi-over-sigmas-mtype arg-ty (mtype-sigma head-ty tail-ty)) ctx)
                (fwd (rev output))
                output

        rev-fwd = ?
    
    
distribute-pi-over-sigmas-iso arg-ty res-ty ctx =
    MkIso fwd rev fwd-rev rev-fwd
    where
        fwd :
            (input : (Decode (mtype-pi arg-ty res-ty) ctx)) ->
            (Decode (distribute-pi-over-sigmas-mtype arg-ty res-ty) ctx)
            
        fwd = ?

        rev :
            (output : Decode (distribute-pi-over-sigmas-mtype arg-ty res-ty) ctx) ->
            (Decode (mtype-pi arg-ty res-ty) ctx)
        rev = ?

        fwd-rev :
            (input : (Decode (mtype-pi arg-ty res-ty) ctx)) ->
            ObsEqual
                ((Decode (mtype-pi arg-ty res-ty) ctx))
                (rev (fwd input))
                input

        fwd-rev = ?

        rev-fwd :
            (output : Decode (distribute-pi-over-sigmas-mtype arg-ty res-ty) ctx) ->
            ObsEqual
                (Decode (distribute-pi-over-sigmas-mtype arg-ty res-ty) ctx)
                (fwd (rev output))
                output

        rev-fwd = ?
    

