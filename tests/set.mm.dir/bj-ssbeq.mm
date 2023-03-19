include "weq.mm"
include "wssb.mm"
include "wi.mm"
include "wal.mm"
include "df-ssb.mm"
include "wex.mm"
include "19.23v.mm"
include "ax6ev.mm"
include "pm2.27.mm"
include "ax-mp.mm"
include "ax-1.mm"
include "impbii.mm"
include "bitri.mm"
include "imbi2i.mm"
include "albii.mm"

theorem bj-ssbeq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint u y
  disjoint u x
  disjoint u z
  disjoint t u
  assert |- ( [b t /b x ]b y = z <-> y = z )

  proof
    vy
    vz
    weq
    #
    vx
    vt
    wssb
    vu
    vt
    weq
    #
    vx
    vu
    weq
    #
    @0
    wi
    vx
    wal
    #
    wi
    #
    vu
    wal
    #
    @0
    @0
    vx
    vu
    vt
    df-ssb
    @5
    @1
    @0
    wi
    #
    vu
    wal
    #
    @0
    @4
    @6
    vu
    @3
    @0
    @1
    @3
    @2
    vx
    wex
    #
    @0
    wi
    #
    @0
    @2
    @0
    vx
    19.23v
    @9
    @0
    @8
    @9
    @0
    wi
    vx
    vu
    ax6ev
    @8
    @0
    pm2.27
    ax-mp
    @0
    @8
    ax-1
    impbii
    bitri
    imbi2i
    albii
    @7
    @1
    vu
    wex
    #
    @0
    wi
    #
    @0
    @1
    @0
    vu
    19.23v
    @11
    @0
    @10
    @11
    @0
    wi
    vu
    vt
    ax6ev
    @10
    @0
    pm2.27
    ax-mp
    @0
    @10
    ax-1
    impbii
    bitri
    bitri
    bitri
end
