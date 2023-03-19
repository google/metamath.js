include "weq.mm"
include "wex.mm"
include "wal.mm"
include "w3o.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "nfeqf.mm"
include "19.9d.mm"
include "impancom.mm"
include "orrd.mm"
include "expcom.mm"
include "3orrot.mm"
include "3orass.mm"
include "bitri.mm"
include "sylibr.mm"
include "19.8a.mm"
include "wi.mm"
include "ax6e.mm"
include "ax7.mm"
include "com12.mm"
include "eximii.mm"
include "19.35i.mm"
include "3jaoi.mm"
include "impbii.mm"

theorem wl-exeq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( E. x y = z <-> ( y = z \/ A. x x = y \/ A. x x = z ) )

  proof
    vy
    vz
    weq
    #
    vx
    wex
    #
    @0
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    #
    vx
    wal
    #
    w3o
    #
    @1
    @3
    @5
    @0
    wo
    #
    wo
    #
    @6
    @1
    @3
    @7
    @3
    wn
    #
    @1
    @7
    @9
    @1
    wa
    @5
    @0
    @9
    @5
    wn
    #
    @1
    @0
    @0
    @9
    @10
    wa
    vx
    vy
    vz
    vx
    nfeqf
    19.9d
    impancom
    orrd
    expcom
    orrd
    @6
    @3
    @5
    @0
    w3o
    @8
    @0
    @3
    @5
    3orrot
    @3
    @5
    @0
    3orass
    bitri
    sylibr
    @0
    @1
    @3
    @5
    @0
    vx
    19.8a
    @2
    @0
    vx
    @4
    @2
    @0
    wi
    vx
    vx
    vz
    ax6e
    @2
    @4
    @0
    vx
    vy
    vz
    ax7
    #
    com12
    eximii
    19.35i
    @4
    @0
    vx
    @2
    @4
    @0
    wi
    vx
    vx
    vy
    ax6e
    @11
    eximii
    19.35i
    3jaoi
    impbii
end
