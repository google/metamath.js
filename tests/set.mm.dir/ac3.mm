include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "ac2.mm"
include "aceq2.mm"
include "mpbi.mm"

theorem ac3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  assert |- E. y A. z e. x ( z =/= (/) -> E! w e. z E. v e. y ( z e. v /\ w e. v ) )

  proof
    vz
    vu
    wel
    vv
    vu
    wel
    wa
    vu
    vy
    cv
    #
    wrex
    vv
    vz
    cv
    #
    wreu
    vw
    @1
    wral
    vz
    vx
    cv
    #
    wral
    vy
    wex
    @1
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
    @0
    wrex
    vw
    @1
    wreu
    wi
    vz
    @2
    wral
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    vu
    ac2
    vx
    vy
    vz
    vw
    vv
    vu
    aceq2
    mpbi
end
