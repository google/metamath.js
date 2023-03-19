include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "albi.mm"
include "wi.mm"
include "ax6e.mm"
include "biimpr.mm"
include "ax7.mm"
include "syli.mm"
include "com12.mm"
include "eximii.mm"
include "19.35i.mm"
include "spsd.mm"
include "sps.mm"
include "a1dd.mm"
include "wn.mm"
include "wa.mm"
include "nfeqf.mm"
include "19.9d.mm"
include "ex.mm"
include "bija.mm"
include "sylc.mm"

theorem equvel
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. z ( z = x <-> z = y ) -> x = y )

  proof
    vz
    vx
    weq
    #
    vz
    vy
    weq
    #
    wb
    #
    vz
    wal
    @0
    vz
    wal
    #
    @1
    vz
    wal
    #
    wb
    vx
    vy
    weq
    #
    vz
    wex
    #
    @5
    @0
    @1
    vz
    albi
    @2
    @5
    vz
    @1
    @2
    @5
    wi
    vz
    vz
    vy
    ax6e
    @2
    @1
    @5
    @1
    @2
    @0
    @5
    @0
    @1
    biimpr
    vz
    vx
    vy
    ax7
    #
    syli
    com12
    eximii
    19.35i
    @3
    @4
    @6
    @5
    wi
    #
    @3
    @4
    @5
    @6
    @0
    @4
    @5
    wi
    vz
    @0
    @1
    @5
    vz
    @7
    spsd
    sps
    a1dd
    @3
    wn
    #
    @4
    wn
    #
    @8
    @5
    @9
    @10
    wa
    vz
    vx
    vy
    vz
    nfeqf
    19.9d
    ex
    bija
    sylc
end
