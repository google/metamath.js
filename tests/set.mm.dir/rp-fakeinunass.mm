include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "wss.mm"
include "cin.mm"
include "cun.mm"
include "wceq.mm"
include "rp-fakeanorass.mm"
include "albii.mm"
include "dfss2.mm"
include "dfcleq.mm"
include "elun.mm"
include "elin.mm"
include "orbi1i.mm"
include "bitri.mm"
include "anbi2i.mm"
include "bibi12i.mm"
include "3bitr4i.mm"

theorem rp-fakeinunass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( C C_ A <-> ( ( A i^i B ) u. C ) = ( A i^i ( B u. C ) ) )

  proof
    vx
    cv
    #
    cC
    wcel
    #
    @0
    cA
    wcel
    #
    wi
    #
    vx
    wal
    @2
    @0
    cB
    wcel
    #
    wa
    #
    @1
    wo
    #
    @2
    @4
    @1
    wo
    #
    wa
    #
    wb
    #
    vx
    wal
    #
    cC
    cA
    wss
    cA
    cB
    cin
    #
    cC
    cun
    #
    cA
    cB
    cC
    cun
    #
    cin
    #
    wceq
    #
    @3
    @9
    vx
    @2
    @4
    @1
    rp-fakeanorass
    albii
    vx
    cC
    cA
    dfss2
    @15
    @0
    @12
    wcel
    #
    @0
    @14
    wcel
    #
    wb
    #
    vx
    wal
    @10
    vx
    @12
    @14
    dfcleq
    @18
    @9
    vx
    @16
    @6
    @17
    @8
    @16
    @0
    @11
    wcel
    #
    @1
    wo
    @6
    @0
    @11
    cC
    elun
    @19
    @5
    @1
    @0
    cA
    cB
    elin
    orbi1i
    bitri
    @17
    @2
    @0
    @13
    wcel
    #
    wa
    @8
    @0
    cA
    @13
    elin
    @20
    @7
    @2
    @0
    cB
    cC
    elun
    anbi2i
    bitri
    bibi12i
    albii
    bitri
    3bitr4i
end
