include "cv.mm"
include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "wn.mm"
include "wrex.mm"
include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cvv.mm"
include "cstrkg2d.mm"
include "istrkg2d.mm"
include "sylib.mm"
include "simprd.mm"
include "simpld.mm"

theorem axtglowdim2OLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vu: setvar u
  let vv: setvar v
  assume istrkg2d.p: |- P = ( Base ` G )
  assume istrkg2d.d: |- .- = ( dist ` G )
  assume istrkg2d.i: |- I = ( Itv ` G )
  assume axtglowdim2OLD.g: |- ( ph -> G e. TarskiG2D )

  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- d
  disjoint .- f
  disjoint .- i
  disjoint .- p
  disjoint .- u
  disjoint .- v
  disjoint d f
  disjoint d i
  disjoint d p
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f i
  disjoint f p
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i p
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G d
  disjoint G f
  disjoint G i
  disjoint G p
  disjoint I d
  disjoint I f
  disjoint I i
  disjoint I p
  disjoint I u
  disjoint I v
  disjoint P d
  disjoint P f
  disjoint P i
  disjoint P p
  disjoint P u
  disjoint P v
  assert |- ( ph -> E. x e. P E. y e. P E. z e. P -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) )

  proof
    wph
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    co
    wcel
    @1
    @0
    @2
    cI
    co
    wcel
    @2
    @1
    @0
    cI
    co
    wcel
    w3o
    #
    wn
    vz
    cP
    wrex
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    @1
    vu
    cv
    #
    c.mi
    co
    @1
    vv
    cv
    #
    c.mi
    co
    wceq
    @2
    @5
    c.mi
    co
    @2
    @6
    c.mi
    co
    wceq
    @0
    @5
    c.mi
    co
    @0
    @6
    c.mi
    co
    wceq
    w3a
    @5
    @6
    wne
    wa
    @3
    wi
    vv
    cP
    wral
    vu
    cP
    wral
    vz
    cP
    wral
    vy
    cP
    wral
    vx
    cP
    wral
    #
    wph
    cG
    cvv
    wcel
    #
    @4
    @7
    wa
    #
    wph
    cG
    cstrkg2d
    wcel
    @8
    @9
    wa
    axtglowdim2OLD.g
    vx
    vy
    vz
    vv
    vu
    cP
    cG
    cI
    c.mi
    istrkg2d.p
    istrkg2d.d
    istrkg2d.i
    istrkg2d
    sylib
    simprd
    simpld
end
