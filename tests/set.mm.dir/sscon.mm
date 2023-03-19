include "wss.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "ssel.mm"
include "con3d.mm"
include "anim2d.mm"
include "eldif.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem sscon
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( C \ B ) C_ ( C \ A ) )

  proof
    cA
    cB
    wss
    #
    vx
    cC
    cB
    cdif
    #
    cC
    cA
    cdif
    #
    @0
    vx
    cv
    #
    cC
    wcel
    #
    @3
    cB
    wcel
    #
    wn
    #
    wa
    @4
    @3
    cA
    wcel
    #
    wn
    #
    wa
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @6
    @8
    @4
    @0
    @7
    @5
    cA
    cB
    @3
    ssel
    con3d
    anim2d
    @3
    cC
    cB
    eldif
    @3
    cC
    cA
    eldif
    3imtr4g
    ssrdv
end
