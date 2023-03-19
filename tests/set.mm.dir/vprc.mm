include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wal.mm"
include "nalset.mm"
include "wb.mm"
include "vex.mm"
include "tbt.mm"
include "albii.mm"
include "dfcleq.mm"
include "bitr4i.mm"
include "exbii.mm"
include "mtbi.mm"
include "isset.mm"
include "mtbir.mm"

theorem vprc
  let vx: setvar x
  let vy: setvar y


  assert |- -. _V e. _V

  proof
    cvv
    cvv
    wcel
    vx
    cv
    #
    cvv
    wceq
    #
    vx
    wex
    #
    vy
    cv
    #
    @0
    wcel
    #
    vy
    wal
    #
    vx
    wex
    @2
    vx
    vy
    nalset
    @5
    @1
    vx
    @5
    @4
    @3
    cvv
    wcel
    #
    wb
    #
    vy
    wal
    @1
    @4
    @7
    vy
    @6
    @4
    vy
    vex
    tbt
    albii
    vy
    @0
    cvv
    dfcleq
    bitr4i
    exbii
    mtbi
    vx
    cvv
    isset
    mtbir
end
