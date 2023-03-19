include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "axunnd.mm"
include "wceq.mm"
include "elequ2.mm"
include "elequ1.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"

theorem zfcndun
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
  assert |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @1
    vx
    cv
    #
    wcel
    #
    wa
    #
    vw
    wex
    #
    @0
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
    @8
    @7
    @3
    wcel
    #
    wa
    #
    vy
    wex
    #
    @8
    wi
    #
    vz
    wal
    #
    vy
    wex
    vy
    vz
    vx
    axunnd
    @10
    @15
    vy
    @9
    @14
    vz
    @6
    @13
    @8
    @5
    @12
    vw
    vy
    @1
    @7
    wceq
    @2
    @8
    @4
    @11
    vw
    vy
    vz
    elequ2
    vw
    vy
    vx
    elequ1
    anbi12d
    cbvexv
    imbi1i
    albii
    exbii
    mpbir
end
