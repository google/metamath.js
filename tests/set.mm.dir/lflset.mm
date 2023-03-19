include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "elex.mm"
include "clfn.mm"
include "cvsca.mm"
include "cplusg.mm"
include "csca.mm"
include "cmulr.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-lfl.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lflset
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let vf: setvar f
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  assume lflset.v: |- V = ( Base ` W )
  assume lflset.a: |- .+ = ( +g ` W )
  assume lflset.d: |- D = ( Scalar ` W )
  assume lflset.s: |- .x. = ( .s ` W )
  assume lflset.k: |- K = ( Base ` D )
  assume lflset.p: |- .+^ = ( +g ` D )
  assume lflset.t: |- .X. = ( .r ` D )
  assume lflset.f: |- F = ( LFnl ` W )

  disjoint f r
  disjoint K f
  disjoint K r
  disjoint f x
  disjoint f y
  disjoint V f
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint W f
  disjoint r x
  disjoint r y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint .+^ w
  disjoint f w
  disjoint r w
  disjoint K w
  disjoint w x
  disjoint w y
  disjoint V w
  disjoint W w
  disjoint .x. w
  disjoint .+ w
  disjoint .X. w
  assert |- ( W e. X -> F = { f e. ( K ^m V ) | A. r e. K A. x e. V A. y e. V ( f ` ( ( r .x. x ) .+ y ) ) = ( ( r .X. ( f ` x ) ) .+^ ( f ` y ) ) } )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cF
    vr
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    vy
    cv
    #
    c.pl
    co
    #
    vf
    cv
    #
    cfv
    #
    @1
    @2
    @6
    cfv
    #
    c.xp
    co
    #
    @4
    @6
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    #
    vf
    cK
    cV
    cmap
    co
    #
    crab
    #
    wceq
    cW
    cX
    elex
    @0
    cF
    cW
    clfn
    cfv
    @17
    lflset.f
    vw
    cW
    @1
    @2
    vw
    cv
    #
    cvsca
    cfv
    #
    co
    #
    @4
    @18
    cplusg
    cfv
    #
    co
    #
    @6
    cfv
    #
    @1
    @8
    @18
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    @10
    @24
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @18
    cbs
    cfv
    #
    wral
    #
    vx
    @30
    wral
    #
    vr
    @24
    cbs
    cfv
    #
    wral
    #
    vf
    @33
    @30
    cmap
    co
    #
    crab
    @17
    cvv
    clfn
    @18
    cW
    wceq
    #
    @34
    @15
    vf
    @35
    @16
    @36
    @33
    cK
    @30
    cV
    cmap
    @36
    @33
    cD
    cbs
    cfv
    cK
    @36
    @24
    cD
    cbs
    @36
    @24
    cW
    csca
    cfv
    cD
    @18
    cW
    csca
    fveq2
    lflset.d
    syl6eqr
    #
    fveq2d
    lflset.k
    syl6eqr
    #
    @36
    @30
    cW
    cbs
    cfv
    cV
    @18
    cW
    cbs
    fveq2
    lflset.v
    syl6eqr
    #
    oveq12d
    @36
    @32
    @14
    vr
    @33
    cK
    @38
    @36
    @31
    @13
    vx
    @30
    cV
    @39
    @36
    @29
    @12
    vy
    @30
    cV
    @39
    @36
    @23
    @7
    @28
    @11
    @36
    @22
    @5
    @6
    @36
    @20
    @3
    @4
    @4
    @21
    c.pl
    @36
    @21
    cW
    cplusg
    cfv
    c.pl
    @18
    cW
    cplusg
    fveq2
    lflset.a
    syl6eqr
    @36
    @19
    c.x
    @1
    @2
    @36
    @19
    cW
    cvsca
    cfv
    c.x
    @18
    cW
    cvsca
    fveq2
    lflset.s
    syl6eqr
    oveqd
    @36
    @4
    eqidd
    oveq123d
    fveq2d
    @36
    @26
    @9
    @10
    @10
    @27
    c.pd
    @36
    @27
    cD
    cplusg
    cfv
    c.pd
    @36
    @24
    cD
    cplusg
    @37
    fveq2d
    lflset.p
    syl6eqr
    @36
    @25
    c.xp
    @1
    @8
    @36
    @25
    cD
    cmulr
    cfv
    c.xp
    @36
    @24
    cD
    cmulr
    @37
    fveq2d
    lflset.t
    syl6eqr
    oveqd
    @36
    @10
    eqidd
    oveq123d
    eqeq12d
    raleqbidv
    raleqbidv
    raleqbidv
    rabeqbidv
    vx
    vy
    vw
    vf
    vr
    df-lfl
    @15
    vf
    @16
    cK
    cV
    cmap
    ovex
    rabex
    fvmpt
    syl5eq
    syl
end
