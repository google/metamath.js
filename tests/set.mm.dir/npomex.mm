include "cnp.mm"
include "wcel.mm"
include "cfn.mm"
include "cvv.mm"
include "wne.mm"
include "com.mm"
include "wn.mm"
include "elex.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "prnmax.mm"
include "ralrimiva.mm"
include "wa.mm"
include "wor.mm"
include "c0.mm"
include "cnq.mm"
include "wss.mm"
include "prpssnq.mm"
include "pssssd.mm"
include "ltsonq.mm"
include "soss.mm"
include "mpisyl.mm"
include "adantr.mm"
include "simpr.mm"
include "prn0.mm"
include "fimax2g.mm"
include "syl3anc.mm"
include "ralnex.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"
include "ex.mm"
include "mt2d.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "necomd.mm"
include "fineqv.mm"
include "necon1abii.mm"

theorem npomex
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. P. -> _om e. _V )

  proof
    cA
    cnp
    wcel
    #
    cfn
    cvv
    wne
    com
    cvv
    wcel
    #
    @0
    cvv
    cfn
    @0
    cA
    cvv
    wcel
    cA
    cfn
    wcel
    #
    wn
    cvv
    cfn
    wne
    cA
    cnp
    elex
    @0
    @2
    vx
    cv
    #
    vy
    cv
    cltq
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wral
    #
    @0
    @5
    vx
    cA
    vy
    cA
    @3
    prnmax
    ralrimiva
    @0
    @2
    @6
    wn
    #
    @0
    @2
    wa
    #
    @4
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @7
    @8
    cA
    cltq
    wor
    #
    @2
    cA
    c0
    wne
    #
    @10
    @0
    @11
    @2
    @0
    cA
    cnq
    wss
    cnq
    cltq
    wor
    @11
    @0
    cA
    cnq
    cA
    prpssnq
    pssssd
    ltsonq
    cA
    cnq
    cltq
    soss
    mpisyl
    adantr
    @0
    @2
    simpr
    @0
    @12
    @2
    cA
    prn0
    adantr
    vx
    vy
    cA
    cltq
    fimax2g
    syl3anc
    @10
    @5
    wn
    #
    vx
    cA
    wrex
    @7
    @9
    @13
    vx
    cA
    @4
    vy
    cA
    ralnex
    rexbii
    @5
    vx
    cA
    rexnal
    bitri
    sylib
    ex
    mt2d
    cA
    cvv
    cfn
    nelne1
    syl2anc
    necomd
    @1
    cfn
    cvv
    fineqv
    necon1abii
    sylib
end
