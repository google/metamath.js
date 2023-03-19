include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "weu.mm"
include "wex.mm"
include "dfac5.mm"
include "axaci.mm"

theorem ac8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint w y
  disjoint v y
  disjoint v w
  assert |- ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) )

  proof
    vz
    cv
    #
    c0
    wne
    vz
    vx
    cv
    #
    wral
    @0
    vw
    cv
    #
    wne
    @0
    @2
    cin
    c0
    wceq
    wi
    vw
    @1
    wral
    vz
    @1
    wral
    wa
    vv
    cv
    @0
    vy
    cv
    cin
    wcel
    vv
    weu
    vz
    @1
    wral
    vy
    wex
    wi
    vx
    vx
    vy
    vz
    vw
    vv
    dfac5
    axaci
end
