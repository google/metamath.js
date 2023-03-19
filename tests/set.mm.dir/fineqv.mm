include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cfn.mm"
include "wceq.mm"
include "wss.mm"
include "ssv.mm"
include "a1i.mm"
include "cv.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "vex.mm"
include "fineqvlem.mm"
include "mpan.mm"
include "reldom.mm"
include "brrelexi.mm"
include "syl.mm"
include "con1i.mm"
include "a1d.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ominf.mm"
include "eleq2.mm"
include "mtbii.mm"
include "impbii.mm"

theorem fineqv
  let va: setvar a


  assert |- ( -. _om e. _V <-> Fin = _V )

  proof
    com
    cvv
    wcel
    #
    wn
    #
    cfn
    cvv
    wceq
    #
    @1
    cfn
    cvv
    cfn
    cvv
    wss
    @1
    cfn
    ssv
    a1i
    @1
    va
    cvv
    cfn
    @1
    va
    cv
    #
    cfn
    wcel
    #
    @3
    cvv
    wcel
    #
    @4
    @0
    @4
    wn
    #
    com
    @3
    cpw
    cpw
    #
    cdom
    wbr
    #
    @0
    @5
    @6
    @8
    va
    vex
    @3
    cvv
    fineqvlem
    mpan
    com
    @7
    cdom
    reldom
    brrelexi
    syl
    con1i
    a1d
    ssrdv
    eqssd
    @2
    com
    cfn
    wcel
    @0
    ominf
    cfn
    cvv
    com
    eleq2
    mtbii
    impbii
end
