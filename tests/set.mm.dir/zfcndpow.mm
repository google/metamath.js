include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wceq.mm"
include "wn.mm"
include "dtru.mm"
include "exnal.mm"
include "mpbir.mm"
include "nfe1.mm"
include "axpownd.mm"
include "exlimi.mm"
include "ax-mp.mm"
include "19.9v.mm"
include "19.3v.mm"
include "imbi12i.mm"
include "albii.mm"
include "imbi1i.mm"
include "exbii.mm"
include "mpbi.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "cbvalv.mm"

theorem zfcndpow
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
  assert |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )

  proof
    vw
    cv
    #
    vz
    cv
    #
    wcel
    #
    @0
    vx
    cv
    #
    wcel
    #
    wi
    #
    vw
    wal
    #
    @1
    vy
    cv
    #
    wcel
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    @7
    @1
    wcel
    #
    @7
    @3
    wcel
    #
    wi
    #
    vy
    wal
    #
    @8
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    @11
    vx
    wex
    #
    @12
    vz
    wal
    #
    wi
    #
    vy
    wal
    #
    @8
    wi
    #
    vz
    wal
    #
    vy
    wex
    #
    @17
    @7
    @1
    wceq
    #
    wn
    #
    vy
    wex
    #
    @24
    @27
    @25
    vy
    wal
    wn
    vy
    vz
    dtru
    @25
    vy
    exnal
    mpbir
    @26
    @24
    vy
    @23
    vy
    nfe1
    vy
    vz
    vx
    axpownd
    exlimi
    ax-mp
    @23
    @16
    vy
    @22
    @15
    vz
    @21
    @14
    @8
    @20
    @13
    vy
    @18
    @11
    @19
    @12
    @11
    vx
    19.9v
    @12
    vz
    19.3v
    imbi12i
    albii
    imbi1i
    albii
    exbii
    mpbi
    @10
    @16
    vy
    @9
    @15
    vz
    @6
    @14
    @8
    @5
    @13
    vw
    vy
    @0
    @7
    wceq
    @2
    @11
    @4
    @12
    vw
    vy
    vz
    elequ1
    vw
    vy
    vx
    elequ1
    imbi12d
    cbvalv
    imbi1i
    albii
    exbii
    mpbir
end
