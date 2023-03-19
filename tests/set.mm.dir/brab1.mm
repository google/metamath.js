include "cv.mm"
include "wbr.mm"
include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "breq1.mm"
include "sbcie2g.mm"
include "ax-mp.mm"
include "df-sbc.mm"
include "bitr3i.mm"

theorem brab1
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cR: class R
  let vy: setvar y

  disjoint A z
  disjoint R z
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint R y
  assert |- ( x R A <-> x e. { z | z R A } )

  proof
    vx
    cv
    #
    cA
    cR
    wbr
    #
    vz
    cv
    #
    cA
    cR
    wbr
    #
    vz
    @0
    wsbc
    #
    @0
    @3
    vz
    cab
    wcel
    @0
    cvv
    wcel
    @4
    @1
    wb
    vx
    vex
    @3
    vy
    cv
    #
    cA
    cR
    wbr
    @1
    vz
    vy
    @0
    cvv
    @2
    @5
    cA
    cR
    breq1
    @5
    @0
    cA
    cR
    breq1
    sbcie2g
    ax-mp
    @3
    vz
    @0
    df-sbc
    bitr3i
end
