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
include "citv.mm"
include "cfv.mm"
include "wsbc.mm"
include "cds.mm"
include "cbs.mm"
include "cstrkg2d.mm"
include "simp1.mm"
include "eqcomd.mm"
include "simp3.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "3orbi123d.mm"
include "notbid.mm"
include "rexeqbidv.mm"
include "simp2.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "sbcie3s.mm"
include "df-trkg2d.mm"
include "elab4g.mm"

theorem istrkg2d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  assume istrkg2d.p: |- P = ( Base ` G )
  assume istrkg2d.d: |- .- = ( dist ` G )
  assume istrkg2d.i: |- I = ( Itv ` G )

  disjoint .- u
  disjoint .- v
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint I u
  disjoint I v
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- d
  disjoint .- f
  disjoint .- i
  disjoint .- p
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
  disjoint G d
  disjoint G f
  disjoint G i
  disjoint G p
  disjoint I d
  disjoint I f
  disjoint I i
  disjoint I p
  disjoint P d
  disjoint P f
  disjoint P i
  disjoint P p
  assert |- ( G e. TarskiG2D <-> ( G e. _V /\ ( E. x e. P E. y e. P E. z e. P -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) /\ A. x e. P A. y e. P A. z e. P A. u e. P A. v e. P ( ( ( ( x .- u ) = ( x .- v ) /\ ( y .- u ) = ( y .- v ) /\ ( z .- u ) = ( z .- v ) ) /\ u =/= v ) -> ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) ) ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    vi
    cv
    #
    co
    #
    wcel
    #
    @1
    @0
    @2
    @3
    co
    #
    wcel
    #
    @2
    @1
    @0
    @3
    co
    #
    wcel
    #
    w3o
    #
    wn
    #
    vz
    vp
    cv
    #
    wrex
    #
    vy
    @12
    wrex
    #
    vx
    @12
    wrex
    #
    @1
    vu
    cv
    #
    vd
    cv
    #
    co
    #
    @1
    vv
    cv
    #
    @17
    co
    #
    wceq
    #
    @2
    @16
    @17
    co
    #
    @2
    @19
    @17
    co
    #
    wceq
    #
    @0
    @16
    @17
    co
    #
    @0
    @19
    @17
    co
    #
    wceq
    #
    w3a
    #
    @16
    @19
    wne
    #
    wa
    #
    @10
    wi
    #
    vv
    @12
    wral
    #
    vu
    @12
    wral
    #
    vz
    @12
    wral
    #
    vy
    @12
    wral
    #
    vx
    @12
    wral
    #
    wa
    #
    vi
    vf
    cv
    #
    citv
    cfv
    wsbc
    vd
    @38
    cds
    cfv
    wsbc
    vp
    @38
    cbs
    cfv
    wsbc
    @0
    @1
    @2
    cI
    co
    #
    wcel
    #
    @1
    @0
    @2
    cI
    co
    #
    wcel
    #
    @2
    @1
    @0
    cI
    co
    #
    wcel
    #
    w3o
    #
    wn
    #
    vz
    cP
    wrex
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    @1
    @16
    c.mi
    co
    #
    @1
    @19
    c.mi
    co
    #
    wceq
    #
    @2
    @16
    c.mi
    co
    #
    @2
    @19
    c.mi
    co
    #
    wceq
    #
    @0
    @16
    c.mi
    co
    #
    @0
    @19
    c.mi
    co
    #
    wceq
    #
    w3a
    #
    @29
    wa
    #
    @45
    wi
    #
    vv
    cP
    wral
    #
    vu
    cP
    wral
    #
    vz
    cP
    wral
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    wa
    #
    vf
    cG
    cstrkg2d
    @67
    @37
    vf
    cP
    c.mi
    cI
    cbs
    cds
    citv
    cG
    vp
    vd
    vi
    istrkg2d.p
    istrkg2d.d
    istrkg2d.i
    @12
    cP
    wceq
    #
    @17
    c.mi
    wceq
    #
    @3
    cI
    wceq
    #
    w3a
    #
    @49
    @15
    @66
    @36
    @71
    @48
    @14
    vx
    cP
    @12
    @71
    @12
    cP
    @68
    @69
    @70
    simp1
    eqcomd
    #
    @71
    @47
    @13
    vy
    cP
    @12
    @72
    @71
    @46
    @11
    vz
    cP
    @12
    @72
    @71
    @45
    @10
    @71
    @40
    @5
    @42
    @7
    @44
    @9
    @71
    @39
    @4
    @0
    @71
    cI
    @3
    @1
    @2
    @71
    @3
    cI
    @68
    @69
    @70
    simp3
    eqcomd
    #
    oveqd
    eleq2d
    @71
    @41
    @6
    @1
    @71
    cI
    @3
    @0
    @2
    @73
    oveqd
    eleq2d
    @71
    @43
    @8
    @2
    @71
    cI
    @3
    @1
    @0
    @73
    oveqd
    eleq2d
    3orbi123d
    #
    notbid
    rexeqbidv
    rexeqbidv
    rexeqbidv
    @71
    @65
    @35
    vx
    cP
    @12
    @72
    @71
    @64
    @34
    vy
    cP
    @12
    @72
    @71
    @63
    @33
    vz
    cP
    @12
    @72
    @71
    @62
    @32
    vu
    cP
    @12
    @72
    @71
    @61
    @31
    vv
    cP
    @12
    @72
    @71
    @60
    @30
    @45
    @10
    @71
    @59
    @28
    @29
    @71
    @52
    @21
    @55
    @24
    @58
    @27
    @71
    @50
    @18
    @51
    @20
    @71
    c.mi
    @17
    @1
    @16
    @71
    @17
    c.mi
    @68
    @69
    @70
    simp2
    eqcomd
    #
    oveqd
    @71
    c.mi
    @17
    @1
    @19
    @75
    oveqd
    eqeq12d
    @71
    @53
    @22
    @54
    @23
    @71
    c.mi
    @17
    @2
    @16
    @75
    oveqd
    @71
    c.mi
    @17
    @2
    @19
    @75
    oveqd
    eqeq12d
    @71
    @56
    @25
    @57
    @26
    @71
    c.mi
    @17
    @0
    @16
    @75
    oveqd
    @71
    c.mi
    @17
    @0
    @19
    @75
    oveqd
    eqeq12d
    3anbi123d
    anbi1d
    @74
    imbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    sbcie3s
    vx
    vy
    vz
    vv
    vu
    vf
    vi
    vp
    vd
    df-trkg2d
    elab4g
end
