include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wal.mm"
include "zfauscl.mm"
include "dfcleq.mm"
include "elin.mm"
include "bibi2i.mm"
include "albii.mm"
include "bitri.mm"
include "exbii.mm"
include "mpbir.mm"
include "issetri.mm"

theorem inex1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume inex1.1: |- A e. _V


  assert |- ( A i^i B ) e. _V

  proof
    vx
    cA
    cB
    cin
    #
    vx
    cv
    #
    @0
    wceq
    #
    vx
    wex
    vy
    cv
    #
    @1
    wcel
    #
    @3
    cA
    wcel
    @3
    cB
    wcel
    #
    wa
    #
    wb
    #
    vy
    wal
    #
    vx
    wex
    @5
    vy
    vx
    cA
    inex1.1
    zfauscl
    @2
    @8
    vx
    @2
    @4
    @3
    @0
    wcel
    #
    wb
    #
    vy
    wal
    @8
    vy
    @1
    @0
    dfcleq
    @10
    @7
    vy
    @9
    @6
    @4
    @3
    cA
    cB
    elin
    bibi2i
    albii
    bitri
    exbii
    mpbir
    issetri
end
