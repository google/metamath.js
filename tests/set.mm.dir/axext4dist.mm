include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wel.mm"
include "wb.mm"
include "wi.mm"
include "axc9.mm"
include "imp.mm"
include "nfnae.mm"
include "nfan.mm"
include "elequ2.mm"
include "a1i.mm"
include "alimd.mm"
include "syld.mm"
include "axextdist.mm"
include "impbid.mm"

theorem axext4dist
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( -. A. z z = x /\ -. A. z z = y ) -> ( x = y <-> A. z ( z e. x <-> z e. y ) ) )

  proof
    vz
    vx
    weq
    vz
    wal
    wn
    #
    vz
    vy
    weq
    vz
    wal
    wn
    #
    wa
    #
    vx
    vy
    weq
    #
    vz
    vx
    wel
    vz
    vy
    wel
    wb
    #
    vz
    wal
    #
    @2
    @3
    @3
    vz
    wal
    #
    @5
    @0
    @1
    @3
    @6
    wi
    vx
    vy
    vz
    axc9
    imp
    @2
    @3
    @4
    vz
    @0
    @1
    vz
    vz
    vx
    vz
    nfnae
    vz
    vy
    vz
    nfnae
    nfan
    @3
    @4
    wi
    @2
    vx
    vy
    vz
    elequ2
    a1i
    alimd
    syld
    vx
    vy
    vz
    axextdist
    impbid
end
