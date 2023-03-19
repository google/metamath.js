include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "zfpair.mm"
include "isseti.mm"
include "wb.mm"
include "dfcleq.mm"
include "vex.mm"
include "elpr.mm"
include "bibi2i.mm"
include "biimpr.mm"
include "sylbi.mm"
include "alimi.mm"
include "eximii.mm"

theorem axpr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint y z
  disjoint w y
  disjoint v x
  disjoint v z
  disjoint v w
  disjoint v y
  assert |- E. z A. w ( ( w = x \/ w = y ) -> w e. z )

  proof
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vw
    cv
    #
    @1
    wceq
    @5
    @2
    wceq
    wo
    #
    @5
    @0
    wcel
    #
    wi
    #
    vw
    wal
    #
    vz
    vz
    @3
    vx
    vy
    zfpair
    isseti
    @4
    @7
    @5
    @3
    wcel
    #
    wb
    #
    vw
    wal
    @9
    vw
    @0
    @3
    dfcleq
    @11
    @8
    vw
    @11
    @7
    @6
    wb
    @8
    @10
    @6
    @7
    @5
    @1
    @2
    vw
    vex
    elpr
    bibi2i
    @7
    @6
    biimpr
    sylbi
    alimi
    sylbi
    eximii
end
