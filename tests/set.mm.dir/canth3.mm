include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "canth2g.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "cardsdom.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem canth3
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( card ` A ) e. ( card ` ~P A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ccrd
    cfv
    cA
    cpw
    #
    ccrd
    cfv
    wcel
    #
    cA
    @1
    csdm
    wbr
    #
    cA
    cV
    canth2g
    @0
    @1
    cvv
    wcel
    @2
    @3
    wb
    cA
    cV
    pwexg
    cA
    @1
    cV
    cvv
    cardsdom
    mpdan
    mpbird
end
