include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "wss.mm"
include "cvv.mm"
include "eqid.mm"
include "txbasex.mm"
include "bastg.mm"
include "syl.mm"
include "adantr.mm"
include "wceq.mm"
include "wrex.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "mp3an3.mm"
include "wb.mm"
include "xpexg.mm"
include "elrnmpt2g.mm"
include "mpbird.mm"
include "adantl.mm"
include "sseldd.mm"
include "txval.mm"
include "eleqtrrd.mm"

theorem txopn
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vu: setvar u
  let vv: setvar v


  assert |- ( ( ( R e. V /\ S e. W ) /\ ( A e. R /\ B e. S ) ) -> ( A X. B ) e. ( R tX S ) )

  proof
    cR
    cV
    wcel
    cS
    cW
    wcel
    wa
    #
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cxp
    #
    vu
    vv
    cR
    cS
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
    cR
    cS
    ctx
    co
    #
    @4
    @10
    @11
    @5
    @0
    @10
    @11
    wss
    #
    @3
    @0
    @10
    cvv
    wcel
    @13
    vu
    vv
    @10
    cR
    cS
    cV
    cW
    @10
    eqid
    #
    txbasex
    @10
    cvv
    bastg
    syl
    adantr
    @3
    @5
    @10
    wcel
    #
    @0
    @3
    @15
    @5
    @8
    wceq
    #
    vv
    cS
    wrex
    vu
    cR
    wrex
    #
    @1
    @2
    @5
    @5
    wceq
    #
    @17
    @5
    eqid
    @16
    @18
    @5
    cA
    @7
    cxp
    #
    wceq
    vu
    vv
    cA
    cB
    cR
    cS
    @6
    cA
    wceq
    @8
    @19
    @5
    @6
    cA
    @7
    xpeq1
    eqeq2d
    @7
    cB
    wceq
    @19
    @5
    @5
    @7
    cB
    cA
    xpeq2
    eqeq2d
    rspc2ev
    mp3an3
    @3
    @5
    cvv
    wcel
    @15
    @17
    wb
    cA
    cB
    cR
    cS
    xpexg
    vu
    vv
    cR
    cS
    @8
    @5
    @9
    cvv
    @9
    eqid
    elrnmpt2g
    syl
    mpbird
    adantl
    sseldd
    @0
    @12
    @11
    wceq
    @3
    vu
    vv
    @10
    cR
    cS
    cV
    cW
    @14
    txval
    adantr
    eleqtrrd
end
