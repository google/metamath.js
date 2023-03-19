include "cv.mm"
include "wss.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "axpow2.mm"
include "bm1.3ii.mm"
include "bicom.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axpow3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. y A. z ( z C_ x <-> z e. y )

  proof
    vz
    cv
    vx
    cv
    wss
    #
    vz
    vy
    wel
    #
    wb
    #
    vz
    wal
    #
    vy
    wex
    @1
    @0
    wb
    #
    vz
    wal
    #
    vy
    wex
    @0
    vy
    vz
    vx
    vy
    vz
    axpow2
    bm1.3ii
    @3
    @5
    vy
    @2
    @4
    vz
    @0
    @1
    bicom
    albii
    exbii
    mpbir
end
