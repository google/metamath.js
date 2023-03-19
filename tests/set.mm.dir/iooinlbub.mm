include "cioo.mm"
include "co.mm"
include "cpr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "disjr.mm"
include "wo.mm"
include "elpri.mm"
include "lbioo.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "ubioo.mm"
include "jaoi.mm"
include "syl.mm"
include "mprgbir.mm"

theorem iooinlbub
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A (,) B ) i^i { A , B } ) = (/)

  proof
    cA
    cB
    cioo
    co
    #
    cA
    cB
    cpr
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
    @1
    vx
    @0
    @1
    disjr
    @2
    @1
    wcel
    @2
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wo
    @4
    @2
    cA
    cB
    elpri
    @5
    @4
    @6
    @5
    @3
    cA
    @0
    wcel
    cA
    cB
    lbioo
    @2
    cA
    @0
    eleq1
    mtbiri
    @6
    @3
    cB
    @0
    wcel
    cA
    cB
    ubioo
    @2
    cB
    @0
    eleq1
    mtbiri
    jaoi
    syl
    mprgbir
end
