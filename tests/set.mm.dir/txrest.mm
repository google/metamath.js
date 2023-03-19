include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cxp.mm"
include "crest.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "txval.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cvv.mm"
include "txbasex.mm"
include "xpexg.mm"
include "tgrest.mm"
include "syl2an.mm"
include "wrex.mm"
include "cab.mm"
include "cin.mm"
include "wb.mm"
include "elrest.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "ad2ant2r.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "ad2ant2l.mm"
include "xpeq2.mm"
include "adantl.mm"
include "rexxfr2d.mm"
include "sylan9bbr.mm"
include "wral.mm"
include "xpex.mm"
include "rgen2w.mm"
include "ineq1.mm"
include "inxp.mm"
include "syl6eq.mm"
include "rexrnmpt2.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "abbi2dv.mm"
include "rnmpt2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"
include "ovex.mm"
include "mp2an.mm"

theorem txrest
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vw: setvar w


  assert |- ( ( ( R e. V /\ S e. W ) /\ ( A e. X /\ B e. Y ) ) -> ( ( R tX S ) |`t ( A X. B ) ) = ( ( R |`t A ) tX ( S |`t B ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    wa
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    wa
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    cA
    cB
    cxp
    #
    crest
    co
    #
    vu
    vv
    cR
    cA
    crest
    co
    #
    cS
    cB
    crest
    co
    #
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    @10
    @11
    ctx
    co
    #
    @6
    @9
    vr
    vs
    cR
    cS
    vr
    cv
    #
    vs
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    @8
    crest
    co
    #
    @23
    @8
    crest
    co
    #
    ctg
    cfv
    #
    @17
    @6
    @7
    @24
    @8
    crest
    @2
    @7
    @24
    wceq
    @5
    vr
    vs
    @23
    cR
    cS
    cV
    cW
    @23
    eqid
    #
    txval
    adantr
    oveq1d
    @2
    @23
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    @27
    @25
    wceq
    @5
    vr
    vs
    @23
    cR
    cS
    cV
    cW
    @28
    txbasex
    #
    cA
    cB
    cX
    cY
    xpexg
    #
    @8
    @23
    cvv
    cvv
    tgrest
    syl2an
    @6
    @26
    @16
    ctg
    @6
    @26
    vx
    cv
    #
    @14
    wceq
    #
    vv
    @11
    wrex
    #
    vu
    @10
    wrex
    #
    vx
    cab
    @16
    @6
    @36
    vx
    @26
    @6
    @33
    @26
    wcel
    #
    @33
    vw
    cv
    #
    @8
    cin
    #
    wceq
    #
    vw
    @23
    wrex
    #
    @36
    @2
    @29
    @30
    @37
    @41
    wb
    @5
    @31
    @32
    vw
    @33
    @8
    @23
    cvv
    cvv
    elrest
    syl2an
    @6
    @36
    @33
    @19
    cA
    cin
    #
    @20
    cB
    cin
    #
    cxp
    #
    wceq
    #
    vs
    cS
    wrex
    #
    vr
    cR
    wrex
    #
    @41
    @6
    @35
    @46
    vu
    vr
    @42
    @10
    cR
    cvv
    @42
    cvv
    wcel
    @6
    @19
    cR
    wcel
    wa
    @19
    cA
    vr
    vex
    #
    inex1
    a1i
    @0
    @3
    @12
    @10
    wcel
    @12
    @42
    wceq
    #
    vr
    cR
    wrex
    wb
    @1
    @4
    vr
    @12
    cA
    cR
    cV
    cX
    elrest
    ad2ant2r
    @49
    @35
    @33
    @42
    @13
    cxp
    #
    wceq
    #
    vv
    @11
    wrex
    @6
    @46
    @49
    @34
    @51
    vv
    @11
    @49
    @14
    @50
    @33
    @12
    @42
    @13
    xpeq1
    eqeq2d
    rexbidv
    @6
    @51
    @45
    vv
    vs
    @43
    @11
    cS
    cvv
    @43
    cvv
    wcel
    @6
    @20
    cS
    wcel
    wa
    @20
    cB
    vs
    vex
    #
    inex1
    a1i
    @1
    @4
    @13
    @11
    wcel
    @13
    @43
    wceq
    #
    vs
    cS
    wrex
    wb
    @0
    @3
    vs
    @13
    cB
    cS
    cW
    cY
    elrest
    ad2ant2l
    @53
    @51
    @45
    wb
    @6
    @53
    @50
    @44
    @33
    @13
    @43
    @42
    xpeq2
    eqeq2d
    adantl
    rexxfr2d
    sylan9bbr
    rexxfr2d
    @21
    cvv
    wcel
    #
    vs
    cS
    wral
    vr
    cR
    wral
    @41
    @47
    wb
    @54
    vr
    vs
    cR
    cS
    @19
    @20
    @48
    @52
    xpex
    rgen2w
    @40
    @45
    vr
    vs
    vw
    cR
    cS
    @21
    @22
    cvv
    @22
    eqid
    @38
    @21
    wceq
    #
    @39
    @44
    @33
    @55
    @39
    @21
    @8
    cin
    @44
    @38
    @21
    @8
    ineq1
    @19
    @20
    cA
    cB
    inxp
    syl6eq
    eqeq2d
    rexrnmpt2
    ax-mp
    syl6bbr
    bitr4d
    abbi2dv
    vu
    vv
    vx
    @10
    @11
    @14
    @15
    @15
    eqid
    rnmpt2
    syl6eqr
    fveq2d
    3eqtr2d
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    @18
    @17
    wceq
    cR
    cA
    crest
    ovex
    cS
    cB
    crest
    ovex
    vu
    vv
    @16
    @10
    @11
    cvv
    cvv
    @16
    eqid
    txval
    mp2an
    syl6eqr
end
