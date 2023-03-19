include "cv.mm"
include "wnel.mm"
include "cab.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wex.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wn.mm"
include "pm5.19.mm"
include "eleq1.mm"
include "df-nel.mm"
include "id.mm"
include "eleq12d.mm"
include "notbid.mm"
include "syl5bb.mm"
include "bibi12d.mm"
include "spv.mm"
include "mto.mm"
include "abeq2.mm"
include "mtbir.mm"
include "nex.mm"
include "isset.mm"
include "nelir.mm"

theorem ru
  let vx: setvar x
  let vy: setvar y


  assert |- { x | x e/ x } e/ _V

  proof
    vx
    cv
    #
    @0
    wnel
    #
    vx
    cab
    #
    cvv
    @2
    cvv
    wcel
    vy
    cv
    #
    @2
    wceq
    #
    vy
    wex
    @4
    vy
    @4
    vx
    vy
    wel
    #
    @1
    wb
    #
    vx
    wal
    #
    @7
    vy
    vy
    wel
    #
    @8
    wn
    #
    wb
    #
    @8
    pm5.19
    @6
    @10
    vx
    vy
    @0
    @3
    wceq
    #
    @5
    @8
    @1
    @9
    @0
    @3
    @3
    eleq1
    @1
    vx
    vx
    wel
    #
    wn
    @11
    @9
    @0
    @0
    df-nel
    @11
    @12
    @8
    @11
    @0
    @3
    @0
    @3
    @11
    id
    #
    @13
    eleq12d
    notbid
    syl5bb
    bibi12d
    spv
    mto
    @1
    vx
    @3
    abeq2
    mtbir
    nex
    vy
    @2
    isset
    mtbir
    nelir
end
