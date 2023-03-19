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
include "a1i.mm"
include "dvelimh.mm"
include "syl.mm"
include "idiALT.mm"
include "alimi.mm"
include "19.41rg.mm"
include "exim.mm"
include "pm3.35.mm"
include "sylancr.mm"
include "excomim.mm"

theorem ax6e2ndALT
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
    wi
    @3
    @8
    vx
    wex
    #
    vy
    wex
    #
    @9
    @3
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
    ax-mp
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
    id
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
    wi
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
    wi
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
    @28
    wi
    #
    @28
    @27
    @7
    wb
    wi
    #
    @28
    id
    @30
    @29
    vz
    vy
    vv
    equequ1
    a1i
    ax-mp
    dvelimh
    syl
    idiALT
    alimi
    syl
    syl
    @5
    @7
    vx
    19.41rg
    syl
    idiALT
    alimi
    syl
    syl
    @13
    @10
    vy
    exim
    syl
    @14
    @11
    pm3.35
    sylancr
    @8
    vy
    vx
    excomim
    syl
    idiALT
end
