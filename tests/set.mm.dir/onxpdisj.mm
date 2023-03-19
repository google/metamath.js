include "con0.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "disj.mm"
include "wo.mm"
include "on0eqel.mm"
include "0nelxp.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "0nelelxp.mm"
include "con2i.mm"
include "jaoi.mm"
include "syl.mm"
include "mprgbir.mm"

theorem onxpdisj
  let vx: setvar x


  assert |- ( On i^i ( _V X. _V ) ) = (/)

  proof
    con0
    cvv
    cvv
    cxp
    #
    cin
    c0
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    wn
    #
    vx
    con0
    vx
    con0
    @0
    disj
    @1
    con0
    wcel
    @1
    c0
    wceq
    #
    c0
    @1
    wcel
    #
    wo
    @3
    @1
    on0eqel
    @4
    @3
    @5
    @4
    @2
    c0
    @0
    wcel
    cvv
    cvv
    0nelxp
    @1
    c0
    @0
    eleq1
    mtbiri
    @2
    @5
    cvv
    cvv
    @1
    0nelelxp
    con2i
    jaoi
    syl
    mprgbir
end
