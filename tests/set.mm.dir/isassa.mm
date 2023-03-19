include "casa.mm"
include "wcel.mm"
include "clmod.mm"
include "crg.mm"
include "cin.mm"
include "ccrg.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "wsbc.mm"
include "cvsca.mm"
include "cbs.mm"
include "csca.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "wb.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "simplr.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "raleqbidv.mm"
include "adantr.mm"
include "sbcied2.mm"
include "df-assa.mm"
include "elrab2.mm"
include "anass.mm"
include "elin.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "3bitr2i.mm"

theorem isassa
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  let cA: class A
  let vf: setvar f
  let vw: setvar w
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let cY: class Y
  assume isassa.v: |- V = ( Base ` W )
  assume isassa.f: |- F = ( Scalar ` W )
  assume isassa.b: |- B = ( Base ` F )
  assume isassa.s: |- .x. = ( .s ` W )
  assume isassa.t: |- .X. = ( .r ` W )

  disjoint r x
  disjoint r y
  disjoint x y
  disjoint B r
  disjoint F r
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  disjoint .X. r
  disjoint .X. x
  disjoint .X. y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint f r
  disjoint f w
  disjoint B f
  disjoint r w
  disjoint B w
  disjoint F f
  disjoint F w
  disjoint f x
  disjoint f y
  disjoint V f
  disjoint w x
  disjoint w y
  disjoint V w
  disjoint X x
  disjoint X y
  disjoint f s
  disjoint f t
  disjoint .x. f
  disjoint r s
  disjoint r t
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint .x. s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint .x. t
  disjoint .x. w
  disjoint .X. f
  disjoint .X. s
  disjoint .X. t
  disjoint .X. w
  disjoint W f
  disjoint W s
  disjoint W t
  disjoint W w
  disjoint Y y
  assert |- ( W e. AssAlg <-> ( ( W e. LMod /\ W e. Ring /\ F e. CRing ) /\ A. r e. B A. x e. V A. y e. V ( ( ( r .x. x ) .X. y ) = ( r .x. ( x .X. y ) ) /\ ( x .X. ( r .x. y ) ) = ( r .x. ( x .X. y ) ) ) ) )

  proof
    cW
    casa
    wcel
    cW
    clmod
    crg
    cin
    #
    wcel
    #
    cF
    ccrg
    wcel
    #
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
    c.xp
    co
    #
    @3
    @4
    @6
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    @4
    @3
    @6
    c.x
    co
    #
    c.xp
    co
    #
    @9
    wceq
    #
    wa
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
    cB
    wral
    #
    wa
    #
    wa
    @1
    @2
    wa
    #
    @17
    wa
    cW
    clmod
    wcel
    #
    cW
    crg
    wcel
    #
    @2
    w3a
    #
    @17
    wa
    vf
    cv
    #
    ccrg
    wcel
    #
    @3
    @4
    vs
    cv
    #
    co
    #
    @6
    vt
    cv
    #
    co
    #
    @3
    @4
    @6
    @27
    co
    #
    @25
    co
    #
    wceq
    #
    @4
    @3
    @6
    @25
    co
    #
    @27
    co
    #
    @30
    wceq
    #
    wa
    #
    vt
    vw
    cv
    #
    cmulr
    cfv
    #
    wsbc
    #
    vs
    @36
    cvsca
    cfv
    #
    wsbc
    #
    vy
    @36
    cbs
    cfv
    #
    wral
    #
    vx
    @41
    wral
    #
    vr
    @23
    cbs
    cfv
    #
    wral
    #
    wa
    #
    vf
    @36
    csca
    cfv
    #
    wsbc
    @18
    vw
    cW
    @0
    casa
    @36
    cW
    wceq
    #
    @46
    @18
    vf
    @47
    cF
    cvv
    @48
    @36
    csca
    fvexd
    @48
    @47
    cW
    csca
    cfv
    cF
    @36
    cW
    csca
    fveq2
    isassa.f
    syl6eqr
    @48
    @23
    cF
    wceq
    #
    wa
    #
    @24
    @2
    @45
    @17
    @50
    @23
    cF
    ccrg
    @48
    @49
    simpr
    #
    eleq1d
    @50
    @43
    @16
    vr
    @44
    cB
    @50
    @44
    cF
    cbs
    cfv
    cB
    @50
    @23
    cF
    cbs
    @51
    fveq2d
    isassa.b
    syl6eqr
    @48
    @43
    @16
    wb
    @49
    @48
    @42
    @15
    vx
    @41
    cV
    @48
    @41
    cW
    cbs
    cfv
    cV
    @36
    cW
    cbs
    fveq2
    isassa.v
    syl6eqr
    #
    @48
    @40
    @14
    vy
    @41
    cV
    @52
    @48
    @38
    @14
    vs
    @39
    cvv
    @48
    @36
    cvsca
    fvexd
    @48
    @25
    @39
    wceq
    #
    wa
    #
    @35
    @14
    vt
    @37
    cvv
    @54
    @36
    cmulr
    fvexd
    @54
    @27
    @37
    wceq
    #
    wa
    #
    @31
    @10
    @34
    @13
    @56
    @28
    @7
    @30
    @9
    @56
    @26
    @5
    @6
    @6
    @27
    c.xp
    @56
    @27
    @37
    c.xp
    @54
    @55
    simpr
    @56
    @37
    cW
    cmulr
    cfv
    #
    c.xp
    @48
    @37
    @57
    wceq
    @53
    @55
    @36
    cW
    cmulr
    fveq2
    ad2antrr
    isassa.t
    syl6eqr
    eqtrd
    #
    @56
    @25
    c.x
    @3
    @4
    @56
    @25
    @39
    c.x
    @48
    @53
    @55
    simplr
    @56
    @39
    cW
    cvsca
    cfv
    #
    c.x
    @48
    @39
    @59
    wceq
    @53
    @55
    @36
    cW
    cvsca
    fveq2
    ad2antrr
    isassa.s
    syl6eqr
    eqtrd
    #
    oveqd
    @56
    @6
    eqidd
    oveq123d
    @56
    @3
    @3
    @29
    @8
    @25
    c.x
    @60
    @56
    @3
    eqidd
    @56
    @27
    c.xp
    @4
    @6
    @58
    oveqd
    oveq123d
    #
    eqeq12d
    @56
    @33
    @12
    @30
    @9
    @56
    @4
    @4
    @32
    @11
    @27
    c.xp
    @58
    @56
    @4
    eqidd
    @56
    @25
    c.x
    @3
    @6
    @60
    oveqd
    oveq123d
    @61
    eqeq12d
    anbi12d
    sbcied
    sbcied
    raleqbidv
    raleqbidv
    adantr
    raleqbidv
    anbi12d
    sbcied2
    vx
    vy
    vw
    vt
    vf
    vs
    vr
    df-assa
    elrab2
    @1
    @2
    @17
    anass
    @19
    @22
    @17
    @19
    @20
    @21
    wa
    #
    @2
    wa
    @22
    @1
    @62
    @2
    cW
    clmod
    crg
    elin
    anbi1i
    @20
    @21
    @2
    df-3an
    bitr4i
    anbi1i
    3bitr2i
end
