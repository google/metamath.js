include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "ccoss.mm"
include "wa.mm"
include "wi.mm"
include "wex.mm"
include "moantr.mm"
include "wb.mm"
include "cvv.mm"
include "brcoss.mm"
include "el2v.mm"
include "anbi12i.mm"
include "3imtr4g.mm"
include "alrimiv.mm"
include "alimi.mm"

theorem trcoss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R x
  disjoint u x
  disjoint R z
  disjoint u z
  disjoint u y
  disjoint x y
  disjoint y z
  assert |- ( A. y E* u u R y -> A. x A. y A. z ( ( x ,~ R y /\ y ,~ R z ) -> x ,~ R z ) )

  proof
    vu
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vu
    wmo
    #
    vy
    wal
    vx
    cv
    #
    @1
    cR
    ccoss
    #
    wbr
    #
    @1
    vz
    cv
    #
    @5
    wbr
    #
    wa
    #
    @4
    @7
    @5
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    @3
    @12
    vy
    @3
    @11
    vz
    @3
    @0
    @4
    cR
    wbr
    #
    @2
    wa
    vu
    wex
    #
    @2
    @0
    @7
    cR
    wbr
    #
    wa
    vu
    wex
    #
    wa
    @13
    @15
    wa
    vu
    wex
    #
    @9
    @10
    @13
    @2
    @15
    vu
    moantr
    @6
    @14
    @8
    @16
    @6
    @14
    wb
    vx
    vy
    vu
    @4
    @1
    cR
    cvv
    cvv
    brcoss
    el2v
    @8
    @16
    wb
    vy
    vz
    vu
    @1
    @7
    cR
    cvv
    cvv
    brcoss
    el2v
    anbi12i
    @10
    @17
    wb
    vx
    vz
    vu
    @4
    @7
    cR
    cvv
    cvv
    brcoss
    el2v
    3imtr4g
    alrimiv
    alimi
    alrimiv
end
