include "weq.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "elequ2.mm"
include "bibi1d.mm"
include "albidv.mm"
include "ax-ext.mm"
include "syl6bir.mm"
include "ax7.mm"
include "syld.mm"
include "ax6ev.mm"
include "exlimiiv.mm"

theorem axext3
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
    vw
    vx
    weq
    #
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
    #
    vx
    vy
    weq
    #
    wi
    vw
    @0
    @4
    vw
    vy
    weq
    #
    @5
    @0
    @4
    vz
    vw
    wel
    #
    @2
    wb
    #
    vz
    wal
    @6
    @0
    @8
    @3
    vz
    @0
    @7
    @1
    @2
    vw
    vx
    vz
    elequ2
    bibi1d
    albidv
    vw
    vy
    vz
    ax-ext
    syl6bir
    vw
    vx
    vy
    ax7
    syld
    vw
    vx
    ax6ev
    exlimiiv
end
