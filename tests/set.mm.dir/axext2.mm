include "wel.mm"
include "wb.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "ax-ext.mm"
include "19.36v.mm"
include "mpbir.mm"

theorem axext2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E. z ( ( z e. x <-> z e. y ) -> x = y )

  proof
    vz
    vx
    wel
    vz
    vy
    wel
    wb
    #
    vx
    vy
    weq
    #
    wi
    vz
    wex
    @0
    vz
    wal
    @1
    wi
    vx
    vy
    vz
    ax-ext
    @0
    @1
    vz
    19.36v
    mpbir
end
