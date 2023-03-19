include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "cun.mm"
include "wb.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "pm2.621.mm"
include "olc.mm"
include "impbid1.mm"
include "anbi2d.mm"
include "eldif.mm"
include "orbi2i.mm"
include "ordi.mm"
include "bitri.mm"
include "elun.mm"
include "anbi1i.mm"
include "3bitr4g.mm"
include "alimi.mm"
include "disj1.mm"
include "dfcleq.mm"
include "3imtr4i.mm"

theorem undif4
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A i^i C ) = (/) -> ( A u. ( B \ C ) ) = ( ( A u. B ) \ C ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cC
    wcel
    wn
    #
    wi
    #
    vx
    wal
    @0
    cA
    cB
    cC
    cdif
    #
    cun
    #
    wcel
    #
    @0
    cA
    cB
    cun
    #
    cC
    cdif
    #
    wcel
    #
    wb
    #
    vx
    wal
    cA
    cC
    cin
    c0
    wceq
    @5
    @8
    wceq
    @3
    @10
    vx
    @3
    @1
    @0
    @4
    wcel
    #
    wo
    #
    @0
    @7
    wcel
    #
    @2
    wa
    #
    @6
    @9
    @3
    @1
    @0
    cB
    wcel
    #
    wo
    #
    @1
    @2
    wo
    #
    wa
    #
    @16
    @2
    wa
    @12
    @14
    @3
    @17
    @2
    @16
    @3
    @17
    @2
    @1
    @2
    pm2.621
    @2
    @1
    olc
    impbid1
    anbi2d
    @12
    @1
    @15
    @2
    wa
    #
    wo
    @18
    @11
    @19
    @1
    @0
    cB
    cC
    eldif
    orbi2i
    @1
    @15
    @2
    ordi
    bitri
    @13
    @16
    @2
    @0
    cA
    cB
    elun
    anbi1i
    3bitr4g
    @0
    cA
    @4
    elun
    @0
    @7
    cC
    eldif
    3bitr4g
    alimi
    vx
    cA
    cC
    disj1
    vx
    @5
    @8
    dfcleq
    3imtr4i
end
