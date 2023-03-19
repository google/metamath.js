include "wss.mm"
include "cdif.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "ssel.mm"
include "pm4.71d.mm"
include "anbi1d.mm"
include "eldif.mm"
include "elin.mm"
include "anbi1i.mm"
include "ancom.mm"
include "anass.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem difin2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ C -> ( A \ B ) = ( ( C \ B ) i^i A ) )

  proof
    cA
    cC
    wss
    #
    vx
    cA
    cB
    cdif
    #
    cC
    cB
    cdif
    #
    cA
    cin
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    wn
    #
    wa
    @5
    @4
    cC
    wcel
    #
    wa
    #
    @6
    wa
    #
    @4
    @1
    wcel
    @4
    @3
    wcel
    #
    @0
    @5
    @8
    @6
    @0
    @5
    @7
    cA
    cC
    @4
    ssel
    pm4.71d
    anbi1d
    @4
    cA
    cB
    eldif
    @10
    @4
    @2
    wcel
    #
    @5
    wa
    @7
    @6
    wa
    #
    @5
    wa
    #
    @9
    @4
    @2
    cA
    elin
    @11
    @12
    @5
    @4
    cC
    cB
    eldif
    anbi1i
    @13
    @5
    @12
    wa
    @9
    @12
    @5
    ancom
    @5
    @7
    @6
    anass
    bitr4i
    3bitri
    3bitr4g
    eqrdv
end
