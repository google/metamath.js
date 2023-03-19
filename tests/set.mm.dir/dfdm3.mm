include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "cop.mm"
include "wcel.mm"
include "df-dm.mm"
include "df-br.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfdm3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- dom A = { x | E. y <. x , y >. e. A }

  proof
    cA
    cdm
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vy
    wex
    #
    vx
    cab
    @0
    @1
    cop
    cA
    wcel
    #
    vy
    wex
    #
    vx
    cab
    vx
    vy
    cA
    df-dm
    @3
    @5
    vx
    @2
    @4
    vy
    @0
    @1
    cA
    df-br
    exbii
    abbii
    eqtri
end
