include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ssel.mm"
include "imim1d.mm"
include "alimdv.mm"
include "dfss2.mm"
include "3imtr4g.mm"

theorem sstr2
  param cA: class A
  param cB: class B
  param cC: class C
  let vx: setvar x


  assert |- ( A C_ B -> ( B C_ C -> A C_ C ) )

  proof
    cA
    cB
    wss
    #
    vx
    cv
    #
    cB
    wcel
    #
    @1
    cC
    wcel
    #
    wi
    #
    vx
    wal
    @1
    cA
    wcel
    #
    @3
    wi
    #
    vx
    wal
    cB
    cC
    wss
    cA
    cC
    wss
    @0
    @4
    @6
    vx
    @0
    @5
    @2
    @3
    cA
    cB
    @1
    ssel
    imim1d
    alimdv
    vx
    cB
    cC
    dfss2
    vx
    cA
    cC
    dfss2
    3imtr4g
end
