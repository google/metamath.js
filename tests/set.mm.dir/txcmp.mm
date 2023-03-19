include "ccmp.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cmptop.mm"
include "txtop.mm"
include "syl2an.mm"
include "cxp.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "wss.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "txuni.mm"
include "adantr.mm"
include "simprr.mm"
include "eqtrd.mm"
include "txcmplem2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "expr.mm"
include "ralrimiva.mm"
include "iscmp.mm"
include "sylanbrc.mm"

theorem txcmp
  let cR: class R
  let cS: class S
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( R e. Comp /\ S e. Comp ) -> ( R tX S ) e. Comp )

  proof
    cR
    ccmp
    wcel
    #
    cS
    ccmp
    wcel
    #
    wa
    #
    cR
    cS
    ctx
    co
    #
    ctop
    wcel
    #
    @3
    cuni
    #
    vw
    cv
    #
    cuni
    #
    wceq
    #
    @5
    vv
    cv
    cuni
    #
    wceq
    #
    vv
    @6
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vw
    @3
    cpw
    #
    wral
    @3
    ccmp
    wcel
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @4
    @1
    cR
    cmptop
    #
    cS
    cmptop
    #
    cR
    cS
    txtop
    syl2an
    @2
    @13
    vw
    @14
    @2
    @6
    @14
    wcel
    #
    @8
    @12
    @2
    @19
    @8
    wa
    #
    wa
    #
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    @9
    wceq
    #
    vv
    @11
    wrex
    @12
    @21
    vv
    cR
    cS
    @6
    @22
    @23
    @22
    eqid
    #
    @23
    eqid
    #
    @0
    @1
    @20
    simpll
    @0
    @1
    @20
    simplr
    @19
    @6
    @3
    wss
    @2
    @8
    @6
    @3
    elpwi
    ad2antrl
    @21
    @24
    @5
    @7
    @2
    @24
    @5
    wceq
    #
    @20
    @0
    @15
    @16
    @28
    @1
    @17
    @18
    cR
    cS
    @22
    @23
    @26
    @27
    txuni
    syl2an
    adantr
    #
    @2
    @19
    @8
    simprr
    eqtrd
    txcmplem2
    @21
    @25
    @10
    vv
    @11
    @21
    @24
    @5
    @9
    @29
    eqeq1d
    rexbidv
    mpbid
    expr
    ralrimiva
    vw
    vv
    @3
    @5
    @5
    eqid
    iscmp
    sylanbrc
end
