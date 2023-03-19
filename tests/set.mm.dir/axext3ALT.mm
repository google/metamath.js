include "wel.mm"
include "wb.mm"
include "wal.mm"
include "weq.mm"
include "wi.mm"
include "elequ2.mm"
include "bibi1d.mm"
include "albidv.mm"
include "equequ1.mm"
include "imbi12d.mm"
include "ax-ext.mm"
include "chvarv.mm"

theorem axext3ALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint w z
  disjoint w x
  disjoint w y
  assert |- ( A. z ( z e. x <-> z e. y ) -> x = y )

  proof
    vz
    vw
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
    #
    vw
    vy
    weq
    #
    wi
    vz
    vx
    wel
    #
    @1
    wb
    #
    vz
    wal
    #
    vx
    vy
    weq
    #
    wi
    vw
    vx
    vw
    vx
    weq
    #
    @3
    @7
    @4
    @8
    @9
    @2
    @6
    vz
    @9
    @0
    @5
    @1
    vw
    vx
    vz
    elequ2
    bibi1d
    albidv
    vw
    vx
    vy
    equequ1
    imbi12d
    vw
    vy
    vz
    ax-ext
    chvarv
end
