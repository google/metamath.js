include "wss.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ssel.mm"
include "anim1d.mm"
include "elin.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem ssrin
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( A i^i C ) C_ ( B i^i C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cC
    cin
    #
    cB
    cC
    cin
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
    wa
    @3
    cB
    wcel
    #
    @5
    wa
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
    anim1d
    @3
    cA
    cC
    elin
    @3
    cB
    cC
    elin
    3imtr4g
    ssrdv
end
