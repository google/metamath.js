include "wel.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cdom.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "wex.mm"
include "cen.mm"
include "ax-groth.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "biantrurd.mm"
include "sbthb.mm"
include "syl6bb.mm"
include "orbi1d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "3anbi3i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axgroth2
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
  assert |- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\ E. w e. y A. v ( v C_ z -> v e. w ) ) /\ A. z ( z C_ y -> ( y ~<_ z \/ z e. y ) ) )

  proof
    vx
    vy
    wel
    #
    vw
    cv
    vz
    cv
    #
    wss
    vw
    vy
    wel
    wi
    vw
    wal
    vv
    cv
    @1
    wss
    vv
    vw
    wel
    wi
    vv
    wal
    vw
    vy
    cv
    #
    wrex
    wa
    vz
    @2
    wral
    #
    @1
    @2
    wss
    #
    @2
    @1
    cdom
    wbr
    #
    vz
    vy
    wel
    #
    wo
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    @0
    @3
    @4
    @1
    @2
    cen
    wbr
    #
    @6
    wo
    #
    wi
    #
    vz
    wal
    #
    w3a
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    ax-groth
    @10
    @15
    vy
    @9
    @14
    @0
    @3
    @8
    @13
    vz
    @4
    @7
    @12
    @4
    @5
    @11
    @6
    @4
    @5
    @1
    @2
    cdom
    wbr
    #
    @5
    wa
    @11
    @4
    @16
    @5
    @2
    cvv
    wcel
    @4
    @16
    wi
    vy
    vex
    @1
    @2
    cvv
    ssdomg
    ax-mp
    biantrurd
    @1
    @2
    sbthb
    syl6bb
    orbi1d
    pm5.74i
    albii
    3anbi3i
    exbii
    mpbir
end
