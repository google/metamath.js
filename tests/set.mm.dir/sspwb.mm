include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "sstr2.mm"
include "com12.mm"
include "vex.mm"
include "elpw.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "csn.mm"
include "ssel.mm"
include "snex.mm"
include "snss.mm"
include "bitr4i.mm"
include "3imtr3g.mm"
include "impbii.mm"

theorem sspwb
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B <-> ~P A C_ ~P B )

  proof
    cA
    cB
    wss
    #
    cA
    cpw
    #
    cB
    cpw
    #
    wss
    #
    @0
    vx
    @1
    @2
    @0
    vx
    cv
    #
    cA
    wss
    #
    @4
    cB
    wss
    #
    @4
    @1
    wcel
    @4
    @2
    wcel
    @5
    @0
    @6
    @4
    cA
    cB
    sstr2
    com12
    @4
    cA
    vx
    vex
    #
    elpw
    @4
    cB
    @7
    elpw
    3imtr4g
    ssrdv
    @3
    vx
    cA
    cB
    @3
    @4
    csn
    #
    @1
    wcel
    #
    @8
    @2
    wcel
    #
    @4
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    @1
    @2
    @8
    ssel
    @9
    @8
    cA
    wss
    @11
    @8
    cA
    @4
    snex
    #
    elpw
    @4
    cA
    @7
    snss
    bitr4i
    @10
    @8
    cB
    wss
    @12
    @8
    cB
    @13
    elpw
    @4
    cB
    @7
    snss
    bitr4i
    3imtr3g
    ssrdv
    impbii
end
