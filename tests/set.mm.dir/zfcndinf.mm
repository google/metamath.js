include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "el.mm"
include "nfv.mm"
include "nfe1.mm"
include "nfim.mm"
include "nfal.mm"
include "nfan.mm"
include "nfex.mm"
include "axinfnd.mm"
include "19.37iv.mm"
include "exlimi.mm"
include "ax-mp.mm"
include "wceq.mm"
include "elequ1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "anbi2i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem zfcndinf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    vz
    cv
    #
    @1
    wcel
    #
    @3
    vw
    cv
    #
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    wa
    #
    vy
    wex
    @2
    @2
    @0
    @5
    wcel
    #
    @7
    wa
    #
    vw
    wex
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    vy
    wex
    #
    @13
    vw
    wex
    @19
    vx
    vw
    el
    @13
    @19
    vw
    @18
    vw
    vy
    @2
    @17
    vw
    @2
    vw
    nfv
    #
    @16
    vw
    vx
    @2
    @15
    vw
    @20
    @14
    vw
    nfe1
    nfim
    nfal
    nfan
    nfex
    @13
    @18
    vy
    vy
    vx
    vw
    axinfnd
    19.37iv
    exlimi
    ax-mp
    @12
    @18
    vy
    @11
    @17
    @2
    @10
    @16
    vz
    vx
    @3
    @0
    wceq
    #
    @4
    @2
    @9
    @15
    vz
    vx
    vy
    elequ1
    @21
    @8
    @14
    vw
    @21
    @6
    @13
    @7
    vz
    vx
    vw
    elequ1
    anbi1d
    exbidv
    imbi12d
    cbvalv
    anbi2i
    exbii
    mpbir
end
