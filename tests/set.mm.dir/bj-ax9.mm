include "weq.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "cv.mm"
include "ax-ext.mm"
include "df-cleq.mm"
include "biimp.mm"
include "sps.mm"
include "sylbi.mm"

theorem bj-ax9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint u w
  disjoint u z
  disjoint w z
  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    weq
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wb
    #
    vz
    wal
    @0
    @1
    wi
    #
    vz
    vu
    vw
    vx
    cv
    vy
    cv
    vu
    vw
    vz
    ax-ext
    df-cleq
    @2
    @3
    vz
    @0
    @1
    biimp
    sps
    sylbi
end
