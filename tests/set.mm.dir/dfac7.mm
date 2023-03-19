include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "dfac2.mm"
include "aceq2.mm"
include "albii.mm"
include "bitr4i.mm"

theorem dfac7
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint v w
  disjoint u w
  disjoint u v
  assert |- ( CHOICE <-> A. x E. y A. z e. x A. w e. z E! v e. z E. u e. y ( z e. u /\ v e. u ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    vz
    vv
    wel
    vw
    vv
    wel
    wa
    vv
    vy
    cv
    #
    wrex
    vw
    @0
    wreu
    wi
    vz
    vx
    cv
    #
    wral
    vy
    wex
    #
    vx
    wal
    vz
    vu
    wel
    vv
    vu
    wel
    wa
    vu
    @1
    wrex
    vv
    @0
    wreu
    vw
    @0
    wral
    vz
    @2
    wral
    vy
    wex
    #
    vx
    wal
    vx
    vy
    vz
    vw
    vv
    dfac2
    @4
    @3
    vx
    vx
    vy
    vz
    vw
    vv
    vu
    aceq2
    albii
    bitr4i
end
