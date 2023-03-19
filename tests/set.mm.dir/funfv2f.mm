include "wfun.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "cuni.mm"
include "funfv2.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2.mm"
include "cbvab.mm"
include "unieqi.mm"
include "syl6eq.mm"

theorem funfv2f
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vw: setvar w
  assume funfv2f.1: |- F/_ y A
  assume funfv2f.2: |- F/_ y F


  assert |- ( Fun F -> ( F ` A ) = U. { y | A F y } )

  proof
    cF
    wfun
    cA
    cF
    cfv
    cA
    vw
    cv
    #
    cF
    wbr
    #
    vw
    cab
    #
    cuni
    cA
    vy
    cv
    #
    cF
    wbr
    #
    vy
    cab
    #
    cuni
    vw
    cA
    cF
    funfv2
    @2
    @5
    @1
    @4
    vw
    vy
    vy
    cA
    @0
    cF
    funfv2f.1
    funfv2f.2
    vy
    @0
    nfcv
    nfbr
    @4
    vw
    nfv
    @0
    @3
    cA
    cF
    breq2
    cbvab
    unieqi
    syl6eq
end
