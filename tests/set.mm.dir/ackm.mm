include "wac.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "wal.mm"
include "wex.mm"
include "axac3.mm"
include "dfackm.mm"
include "mpbi.mm"

theorem ackm
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
  assert |- A. x E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\ ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) )

  proof
    wac
    vy
    cv
    #
    vx
    cv
    #
    wcel
    #
    vz
    cv
    #
    @0
    wcel
    vv
    cv
    #
    @1
    wcel
    @0
    @4
    wceq
    wn
    wa
    @3
    @4
    wcel
    wa
    wi
    wa
    @2
    wn
    @3
    @1
    wcel
    @4
    @3
    wcel
    @4
    @0
    wcel
    wa
    vu
    cv
    #
    @3
    wcel
    @5
    @0
    wcel
    wa
    @5
    @4
    wceq
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
    vx
    wal
    axac3
    vx
    vy
    vz
    vv
    vu
    dfackm
    mpbi
end
