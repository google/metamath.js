include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-opab.mm"
include "wcel.mm"
include "df-br.mm"
include "eleq1.mm"
include "biimpar.mm"
include "sylan2b.mm"
include "exlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"

theorem opabss
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vz: setvar z

  disjoint R x
  disjoint R y
  disjoint x z
  disjoint R z
  disjoint y z
  assert |- { <. x , y >. | x R y } C_ R

  proof
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    copab
    vz
    cv
    #
    @0
    @1
    cop
    #
    wceq
    #
    @2
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    cab
    cR
    @2
    vx
    vy
    vz
    df-opab
    @7
    vz
    cR
    @6
    @3
    cR
    wcel
    #
    vx
    vy
    @2
    @5
    @4
    cR
    wcel
    #
    @8
    @0
    @1
    cR
    df-br
    @5
    @8
    @9
    @3
    @4
    cR
    eleq1
    biimpar
    sylan2b
    exlimivv
    abssi
    eqsstri
end
