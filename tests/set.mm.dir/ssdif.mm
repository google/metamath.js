include "wss.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "ssel.mm"
include "anim1d.mm"
include "eldif.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem ssdif
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( A \ C ) C_ ( B \ C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cC
    cdif
    #
    cB
    cC
    cdif
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
    wn
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
    eldif
    @3
    cB
    cC
    eldif
    3imtr4g
    ssrdv
end
