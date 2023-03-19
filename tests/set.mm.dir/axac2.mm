include "wel.mm"
include "weq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "wal.mm"
include "wex.mm"
include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "dfac2a.mm"
include "ac3.mm"
include "mpg.mm"
include "dfackm.mm"
include "mpbi.mm"
include "spi.mm"

theorem axac2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint v x
  disjoint u x
  disjoint y z
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint u v
  assert |- E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) )

  proof
    vy
    vx
    wel
    #
    vz
    vy
    wel
    vv
    vx
    wel
    vy
    vv
    weq
    wn
    wa
    vz
    vv
    wel
    wa
    wi
    wa
    @0
    wn
    vz
    vx
    wel
    vv
    vz
    wel
    vv
    vy
    wel
    wa
    vu
    vz
    wel
    vu
    vy
    wel
    wa
    vu
    vv
    weq
    wi
    wa
    wi
    wa
    wo
    vu
    wal
    vv
    wex
    vz
    wal
    vy
    wex
    #
    vx
    wac
    @1
    vx
    wal
    vz
    cv
    #
    c0
    wne
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
    wrex
    vv
    @2
    wreu
    wi
    vz
    vx
    cv
    wral
    vy
    wex
    wac
    vx
    vx
    vy
    vz
    vv
    vu
    dfac2a
    vx
    vy
    vz
    vv
    vu
    ac3
    mpg
    vx
    vy
    vz
    vv
    vu
    dfackm
    mpbi
    spi
end
