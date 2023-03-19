include "wal.mm"
include "wsb.mm"
include "wi.mm"
include "2stdpc4.mm"
include "gen2.mm"
include "nfv.mm"
include "nfal.mm"
include "2stdpc5.mm"
include "ax-mp.mm"
include "nfsb.mm"
include "sb8.mm"
include "albii.mm"
include "sylibr.mm"
include "sbal.mm"

theorem ax11-pm2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint t x
  disjoint y z
  disjoint t y
  disjoint t z
  disjoint ph z
  disjoint ph t
  assert |- ( A. x A. y ph -> A. y A. x ph )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    #
    wph
    vx
    wal
    #
    vy
    vt
    wsb
    #
    vt
    wal
    #
    @2
    vy
    wal
    @1
    wph
    vy
    vt
    wsb
    #
    vx
    wal
    #
    vt
    wal
    #
    @4
    @1
    @5
    vx
    vz
    wsb
    #
    vz
    wal
    #
    vt
    wal
    #
    @7
    @1
    @8
    wi
    #
    vz
    wal
    vt
    wal
    @1
    @10
    wi
    @11
    vt
    vz
    wph
    vx
    vy
    vz
    vt
    2stdpc4
    gen2
    @1
    @8
    vt
    vz
    @0
    vt
    vx
    wph
    vt
    vy
    wph
    vt
    nfv
    #
    nfal
    nfal
    @0
    vz
    vx
    wph
    vz
    vy
    wph
    vz
    nfv
    #
    nfal
    nfal
    2stdpc5
    ax-mp
    @6
    @9
    vt
    @5
    vx
    vz
    wph
    vy
    vt
    vz
    @13
    nfsb
    sb8
    albii
    sylibr
    @3
    @6
    vt
    wph
    vx
    vy
    vt
    sbal
    albii
    sylibr
    @2
    vy
    vt
    wph
    vt
    vx
    @12
    nfal
    sb8
    sylibr
end
