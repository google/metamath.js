include "wss.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "ssel.mm"
include "orim1d.mm"
include "elun.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem unss1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( A u. C ) C_ ( B u. C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cC
    cun
    #
    cB
    cC
    cun
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cC
    wcel
    #
    wo
    @3
    cB
    wcel
    #
    @5
    wo
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @4
    @6
    @5
    cA
    cB
    @3
    ssel
    orim1d
    @3
    cA
    cC
    elun
    @3
    cB
    cC
    elun
    3imtr4g
    ssrdv
end
