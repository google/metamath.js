include "cvv.mm"
include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "fncnvima2.mm"
include "wa.mm"
include "fvexd.mm"
include "biantrud.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "eqtrd.mm"

theorem fncnvimaeqv
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( F Fn _V -> ( `' F " _V ) = _V )

  proof
    cF
    cvv
    wfn
    #
    cF
    ccnv
    cvv
    cima
    vy
    cv
    #
    cF
    cfv
    #
    cvv
    wcel
    #
    vy
    cvv
    crab
    #
    cvv
    vy
    cvv
    cvv
    cF
    fncnvima2
    @0
    vx
    @4
    cvv
    @0
    vx
    cv
    #
    cvv
    wcel
    #
    @6
    @5
    cF
    cfv
    #
    cvv
    wcel
    #
    wa
    @5
    @4
    wcel
    @0
    @8
    @6
    @0
    @5
    cF
    fvexd
    biantrud
    @3
    @8
    vy
    @5
    cvv
    vy
    vx
    weq
    @2
    @7
    cvv
    @1
    @5
    cF
    fveq2
    eleq1d
    elrab
    syl6rbbr
    eqrdv
    eqtrd
end
