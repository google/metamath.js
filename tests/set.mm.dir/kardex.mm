include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "cab.mm"
include "wral.mm"
include "crab.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "df-rab.mm"
include "vex.mm"
include "breq1.mm"
include "elab.mm"
include "ralab.mm"
include "anbi12i.mm"
include "abbii.mm"
include "eqtri.mm"
include "scottex.mm"
include "eqeltrri.mm"

theorem kardex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- { x | ( x ~~ A /\ A. y ( y ~~ A -> ( rank ` x ) C_ ( rank ` y ) ) ) } e. _V

  proof
    vx
    cv
    #
    crnk
    cfv
    vy
    cv
    #
    crnk
    cfv
    wss
    #
    vy
    vz
    cv
    #
    cA
    cen
    wbr
    #
    vz
    cab
    #
    wral
    #
    vx
    @5
    crab
    #
    @0
    cA
    cen
    wbr
    #
    @1
    cA
    cen
    wbr
    #
    @2
    wi
    vy
    wal
    #
    wa
    #
    vx
    cab
    #
    cvv
    @7
    @0
    @5
    wcel
    #
    @6
    wa
    #
    vx
    cab
    @12
    @6
    vx
    @5
    df-rab
    @14
    @11
    vx
    @13
    @8
    @6
    @10
    @4
    @8
    vz
    @0
    vx
    vex
    @3
    @0
    cA
    cen
    breq1
    elab
    @4
    @9
    @2
    vy
    vz
    @3
    @1
    cA
    cen
    breq1
    ralab
    anbi12i
    abbii
    eqtri
    vx
    vy
    @5
    scottex
    eqeltrri
end
