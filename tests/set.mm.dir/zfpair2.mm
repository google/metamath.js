include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "wcel.mm"
include "wo.mm"
include "wb.mm"
include "wal.mm"
include "ax-pr.mm"
include "bm1.3ii.mm"
include "dfcleq.mm"
include "vex.mm"
include "elpr.mm"
include "bibi2i.mm"
include "albii.mm"
include "bitri.mm"
include "exbii.mm"
include "mpbir.mm"
include "issetri.mm"

theorem zfpair2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- { x , y } e. _V

  proof
    vz
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    vz
    cv
    #
    @2
    wceq
    #
    vz
    wex
    vw
    cv
    #
    @3
    wcel
    #
    @5
    @0
    wceq
    @5
    @1
    wceq
    wo
    #
    wb
    #
    vw
    wal
    #
    vz
    wex
    @7
    vz
    vw
    vx
    vy
    vz
    vw
    ax-pr
    bm1.3ii
    @4
    @9
    vz
    @4
    @6
    @5
    @2
    wcel
    #
    wb
    #
    vw
    wal
    @9
    vw
    @3
    @2
    dfcleq
    @11
    @8
    vw
    @10
    @7
    @6
    @5
    @0
    @1
    vw
    vex
    elpr
    bibi2i
    albii
    bitri
    exbii
    mpbir
    issetri
end
