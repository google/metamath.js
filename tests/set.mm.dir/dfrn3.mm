include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "cop.mm"
include "wcel.mm"
include "dfrn2.mm"
include "df-br.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfrn3
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ran A = { y | E. x <. x , y >. e. A }

  proof
    cA
    crn
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vx
    wex
    #
    vy
    cab
    @0
    @1
    cop
    cA
    wcel
    #
    vx
    wex
    #
    vy
    cab
    vx
    vy
    cA
    dfrn2
    @3
    @5
    vy
    @2
    @4
    vx
    @0
    @1
    cA
    df-br
    exbii
    abbii
    eqtri
end
