include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "equcomi.mm"
include "axc16.mm"
include "syl5.mm"
include "spsd.mm"
include "exlimiv.mm"
include "wn.mm"
include "alnex.mm"
include "wa.mm"
include "ax6evr.mm"
include "19.29.mm"
include "mpan2.mm"
include "axc9.mm"
include "impcom.mm"
include "axc11r.mm"
include "syl9.mm"
include "aev.mm"
include "syl8.mm"
include "ex.mm"
include "com24.mm"
include "imp.mm"
include "pm2.18.mm"
include "syl6.mm"
include "syl.mm"
include "sylbir.mm"
include "pm2.61i.mm"

theorem axc11n11r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> A. y y = x )

  proof
    vy
    vz
    weq
    vy
    wal
    #
    vz
    wex
    #
    vx
    vy
    weq
    #
    vx
    wal
    #
    vy
    vx
    weq
    #
    vy
    wal
    #
    wi
    #
    @0
    @6
    vz
    @0
    @2
    @5
    vx
    @2
    @4
    @0
    @5
    vx
    vy
    equcomi
    @4
    vy
    vz
    axc16
    syl5
    spsd
    exlimiv
    @1
    wn
    @0
    wn
    #
    vz
    wal
    #
    @6
    @0
    vz
    alnex
    @8
    @7
    vx
    vz
    weq
    #
    wa
    #
    vz
    wex
    #
    @6
    @8
    @9
    vz
    wex
    @11
    vz
    vx
    ax6evr
    @7
    @9
    vz
    19.29
    mpan2
    @10
    @6
    vz
    @10
    @3
    @5
    wn
    #
    @5
    wi
    #
    @5
    @7
    @9
    @3
    @13
    wi
    @7
    @12
    @3
    @9
    @5
    @7
    @12
    @3
    @9
    @5
    wi
    wi
    @7
    @12
    wa
    #
    @3
    @9
    @9
    vx
    wal
    #
    @5
    @14
    @9
    @9
    vy
    wal
    #
    @3
    @15
    @12
    @7
    @9
    @16
    wi
    vx
    vz
    vy
    axc9
    impcom
    @9
    vy
    vx
    axc11r
    syl9
    vx
    vz
    vy
    vx
    vy
    aev
    syl8
    ex
    com24
    imp
    @5
    pm2.18
    syl6
    exlimiv
    syl
    sylbir
    pm2.61i
end
