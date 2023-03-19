include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "ax6e.mm"
include "pm3.2i.mm"
include "19.42v.mm"
include "biimpri.mm"
include "ax-mp.mm"
include "isset.mm"
include "anbi1i.mm"
include "exbii.mm"
include "mpbi.mm"
include "id.mm"
include "hbnae.mm"
include "hbn1.mm"
include "ax-5.mm"
include "wb.mm"
include "equequ1.mm"
include "syl.mm"
include "idiALT.mm"
include "dvelimh.mm"
include "alimi.mm"
include "19.41rg.mm"
include "exim.mm"
include "pm2.27.mm"
include "mpsyl.mm"
include "excomim.mm"

theorem ax6e2nd
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let vz: setvar z

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint y z
  assert |- ( -. A. x x = y -> E. x E. y ( x = u /\ y = v ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    vx
    vu
    weq
    #
    vy
    vv
    weq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    wi
    @1
    @4
    vx
    wex
    #
    vy
    wex
    #
    @5
    @2
    vx
    wex
    #
    @3
    wa
    #
    vy
    wex
    #
    @1
    @10
    @7
    wi
    #
    @7
    vu
    cv
    #
    cvv
    wcel
    #
    @3
    wa
    #
    vy
    wex
    #
    @10
    @13
    @3
    vy
    wex
    #
    wa
    #
    @15
    @13
    @16
    vu
    vex
    vy
    vv
    ax6e
    pm3.2i
    @15
    @17
    @13
    @3
    vy
    19.42v
    biimpri
    ax-mp
    @14
    @9
    vy
    @13
    @8
    @3
    vx
    @12
    isset
    anbi1i
    exbii
    mpbi
    @1
    @9
    @6
    wi
    #
    vy
    wal
    #
    @11
    @1
    @1
    @19
    @1
    id
    #
    @1
    @1
    vy
    wal
    @19
    vx
    vy
    vy
    hbnae
    @1
    @18
    vy
    @1
    @18
    wi
    @1
    @3
    @3
    vx
    wal
    wi
    #
    vx
    wal
    #
    @18
    @1
    @1
    @22
    @20
    @1
    @1
    vx
    wal
    @22
    @0
    vx
    hbn1
    @1
    @21
    vx
    @1
    @21
    wi
    @1
    @1
    @21
    @20
    vz
    vv
    weq
    #
    @3
    vx
    vy
    vz
    @23
    vx
    ax-5
    @3
    vz
    ax-5
    vz
    vy
    weq
    #
    @23
    @3
    wb
    #
    wi
    @24
    @24
    @25
    @24
    id
    vz
    vy
    vv
    equequ1
    syl
    idiALT
    dvelimh
    syl
    idiALT
    alimi
    syl
    syl
    @2
    @3
    vx
    19.41rg
    syl
    idiALT
    alimi
    syl
    syl
    @9
    @6
    vy
    exim
    syl
    @10
    @7
    pm2.27
    mpsyl
    @4
    vy
    vx
    excomim
    syl
    idiALT
end
