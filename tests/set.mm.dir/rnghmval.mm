include "crng.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "cmulr.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "csb.mm"
include "crngh.mm"
include "cvv.mm"
include "cmpt2.mm"
include "df-rnghomo.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "csbeq2dv.mm"
include "sylan9eq.mm"
include "adantl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "oveq12.mm"
include "ancoms.mm"
include "wb.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "adantr.mm"
include "rabeqbidv.mm"
include "csbie2.mm"
include "oveqdr.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eqtrd.mm"
include "simpl.mm"
include "simpr.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2d.mm"

theorem rnghmval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let c.as: class .*
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vk: setvar k
  assume isrnghm.b: |- B = ( Base ` R )
  assume isrnghm.t: |- .x. = ( .r ` R )
  assume isrnghm.m: |- .* = ( .r ` S )
  assume rnghmval.c: |- C = ( Base ` S )
  assume rnghmval.p: |- .+ = ( +g ` R )
  assume rnghmval.a: |- .+b = ( +g ` S )

  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint C f
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint B r
  disjoint B s
  disjoint B v
  disjoint B w
  disjoint f r
  disjoint f s
  disjoint f v
  disjoint f w
  disjoint r s
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint C r
  disjoint C s
  disjoint C v
  disjoint C w
  disjoint R r
  disjoint R s
  disjoint S r
  disjoint S s
  disjoint S v
  disjoint .+ r
  disjoint .+ s
  disjoint .+b r
  disjoint .+b s
  disjoint .x. r
  disjoint .x. s
  disjoint .* r
  disjoint .* s
  disjoint k x
  assert |- ( ( R e. Rng /\ S e. Rng ) -> ( R RngHomo S ) = { f e. ( C ^m B ) | A. x e. B A. y e. B ( ( f ` ( x .+ y ) ) = ( ( f ` x ) .+b ( f ` y ) ) /\ ( f ` ( x .x. y ) ) = ( ( f ` x ) .* ( f ` y ) ) ) } )

  proof
    cR
    crng
    wcel
    #
    cS
    crng
    wcel
    #
    wa
    #
    vr
    vs
    cR
    cS
    crng
    crng
    vv
    vr
    cv
    #
    cbs
    cfv
    #
    vw
    vs
    cv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    cplusg
    cfv
    #
    co
    #
    vf
    cv
    #
    cfv
    #
    @7
    @11
    cfv
    #
    @8
    @11
    cfv
    #
    @5
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    @7
    @8
    @3
    cmulr
    cfv
    #
    co
    #
    @11
    cfv
    #
    @13
    @14
    @5
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vy
    vv
    cv
    #
    wral
    #
    vx
    @25
    wral
    #
    vf
    vw
    cv
    #
    @25
    cmap
    co
    #
    crab
    #
    csb
    #
    csb
    #
    @7
    @8
    c.pl
    co
    #
    @11
    cfv
    #
    @13
    @14
    c.pb
    co
    #
    wceq
    #
    @7
    @8
    c.x
    co
    #
    @11
    cfv
    #
    @13
    @14
    c.as
    co
    #
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vf
    cC
    cB
    cmap
    co
    #
    crab
    #
    crngh
    cvv
    crngh
    vr
    vs
    crng
    crng
    @32
    cmpt2
    wceq
    @2
    vx
    vy
    vw
    vv
    vf
    vs
    vr
    df-rnghomo
    a1i
    @2
    @3
    cR
    wceq
    #
    @5
    cS
    wceq
    #
    wa
    #
    wa
    @32
    vv
    cB
    vw
    cC
    @30
    csb
    #
    csb
    #
    @45
    @48
    @32
    @50
    wceq
    @2
    @46
    @47
    @32
    vv
    cB
    @31
    csb
    @50
    @46
    vv
    @4
    cB
    @31
    @46
    @4
    cR
    cbs
    cfv
    #
    cB
    @3
    cR
    cbs
    fveq2
    isrnghm.b
    syl6eqr
    csbeq1d
    @47
    vv
    cB
    @31
    @49
    @47
    vw
    @6
    cC
    @30
    @47
    @6
    cS
    cbs
    cfv
    #
    cC
    @5
    cS
    cbs
    fveq2
    rnghmval.c
    syl6eqr
    csbeq1d
    csbeq2dv
    sylan9eq
    adantl
    @48
    @50
    @45
    wceq
    @2
    @48
    @50
    @24
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vf
    @44
    crab
    #
    @45
    @50
    @55
    wceq
    @48
    vv
    vw
    cB
    cC
    @30
    @55
    cB
    @51
    cvv
    isrnghm.b
    cR
    cbs
    fvex
    eqeltri
    cC
    @52
    cvv
    rnghmval.c
    cS
    cbs
    fvex
    eqeltri
    @25
    cB
    wceq
    #
    @28
    cC
    wceq
    #
    wa
    @27
    @54
    vf
    @29
    @44
    @57
    @56
    @29
    @44
    wceq
    @28
    cC
    @25
    cB
    cmap
    oveq12
    ancoms
    @56
    @27
    @54
    wb
    @57
    @26
    @53
    vx
    @25
    cB
    @24
    vy
    @25
    cB
    raleq
    raleqbi1dv
    adantr
    rabeqbidv
    csbie2
    a1i
    @48
    @54
    @43
    vf
    @44
    @48
    @53
    @42
    vx
    cB
    @48
    @24
    @41
    vy
    cB
    @48
    @17
    @36
    @23
    @40
    @48
    @12
    @34
    @16
    @35
    @48
    @10
    @33
    @11
    @46
    @47
    vx
    vy
    @9
    c.pl
    @46
    @9
    cR
    cplusg
    cfv
    c.pl
    @3
    cR
    cplusg
    fveq2
    rnghmval.p
    syl6eqr
    oveqdr
    fveq2d
    @48
    @15
    c.pb
    @13
    @14
    @47
    @15
    c.pb
    wceq
    @46
    @47
    @15
    cS
    cplusg
    cfv
    c.pb
    @5
    cS
    cplusg
    fveq2
    rnghmval.a
    syl6eqr
    adantl
    oveqd
    eqeq12d
    @48
    @20
    @38
    @22
    @39
    @48
    @19
    @37
    @11
    @46
    @47
    vx
    vy
    @18
    c.x
    @46
    @18
    cR
    cmulr
    cfv
    c.x
    @3
    cR
    cmulr
    fveq2
    isrnghm.t
    syl6eqr
    oveqdr
    fveq2d
    @48
    @21
    c.as
    @13
    @14
    @47
    @21
    c.as
    wceq
    @46
    @47
    @21
    cS
    cmulr
    cfv
    c.as
    @5
    cS
    cmulr
    fveq2
    isrnghm.m
    syl6eqr
    adantl
    oveqd
    eqeq12d
    anbi12d
    ralbidv
    ralbidv
    rabbidv
    eqtrd
    adantl
    eqtrd
    @0
    @1
    simpl
    @0
    @1
    simpr
    @45
    cvv
    wcel
    @2
    @43
    vf
    @44
    cC
    cB
    cmap
    ovex
    rabex
    a1i
    ovmpt2d
end
