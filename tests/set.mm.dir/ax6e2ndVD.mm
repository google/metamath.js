include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "ax6e.mm"
include "pm3.2i.mm"
include "19.42v.mm"
include "biimpri.mm"
include "e0a.mm"
include "isset.mm"
include "anbi1i.mm"
include "exbii.mm"
include "mpbi.mm"
include "idn1.mm"
include "hbnae.mm"
include "hbn1.mm"
include "ax-5.mm"
include "wb.mm"
include "equequ1.mm"
include "e1a.mm"
include "in1.mm"
include "dvelimh.mm"
include "alimi.mm"
include "syl.mm"
include "19.41rg.mm"
include "exim.mm"
include "pm2.27.mm"
include "e01.mm"
include "excomim.mm"

theorem ax6e2ndVD
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
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wal
    wn
    #
    @0
    vu
    cv
    #
    wceq
    #
    @1
    vv
    cv
    #
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @3
    @8
    vx
    wex
    #
    vy
    wex
    #
    @9
    @5
    vx
    wex
    #
    @7
    wa
    #
    vy
    wex
    #
    @3
    @14
    @11
    wi
    #
    @11
    @4
    cvv
    wcel
    #
    @7
    wa
    #
    vy
    wex
    #
    @14
    @16
    @7
    vy
    wex
    #
    wa
    #
    @18
    @16
    @19
    vu
    vex
    vy
    vv
    ax6e
    pm3.2i
    @18
    @20
    @16
    @7
    vy
    19.42v
    biimpri
    e0a
    @17
    @13
    vy
    @16
    @12
    @7
    vx
    @4
    isset
    anbi1i
    exbii
    mpbi
    @3
    @13
    @10
    wi
    #
    vy
    wal
    #
    @15
    @3
    @3
    @22
    @3
    idn1
    #
    @3
    @3
    vy
    wal
    @22
    vx
    vy
    vy
    hbnae
    @3
    @21
    vy
    @3
    @21
    @3
    @7
    @7
    vx
    wal
    wi
    #
    vx
    wal
    #
    @21
    @3
    @3
    @25
    @23
    @3
    @3
    vx
    wal
    @25
    @2
    vx
    hbn1
    @3
    @24
    vx
    @3
    @24
    @3
    @3
    @24
    @23
    vz
    cv
    #
    @6
    wceq
    #
    @7
    vx
    vy
    vz
    @27
    vx
    ax-5
    @7
    vz
    ax-5
    @26
    @1
    wceq
    #
    @27
    @7
    wb
    #
    @28
    @28
    @29
    @28
    idn1
    vz
    vy
    vv
    equequ1
    e1a
    in1
    dvelimh
    e1a
    in1
    alimi
    syl
    e1a
    @5
    @7
    vx
    19.41rg
    e1a
    in1
    alimi
    syl
    e1a
    @13
    @10
    vy
    exim
    e1a
    @14
    @11
    pm2.27
    e01
    @8
    vy
    vx
    excomim
    e1a
    in1
end
