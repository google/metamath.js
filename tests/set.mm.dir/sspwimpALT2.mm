include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "vex.mm"
include "elpwi.mm"
include "id.mm"
include "sylan9ssr.mm"
include "elpwg.mm"
include "biimpar.mm"
include "sylancr.mm"
include "ex.mm"
include "ssrdv.mm"

theorem sspwimpALT2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B -> ~P A C_ ~P B )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cpw
    #
    cB
    cpw
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    @3
    cvv
    wcel
    #
    @3
    cB
    wss
    #
    @5
    vx
    vex
    @4
    @0
    @3
    cA
    cB
    @3
    cA
    elpwi
    @0
    id
    sylan9ssr
    @6
    @5
    @7
    @3
    cB
    cvv
    elpwg
    biimpar
    sylancr
    ex
    ssrdv
end
