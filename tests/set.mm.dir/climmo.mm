include "cv.mm"
include "cli.mm"
include "wbr.mm"
include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "breq2.mm"
include "cbvexv.mm"
include "climeu.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "df-mo.mm"
include "mpbir.mm"

theorem climmo
  let vx: setvar x
  let cF: class F
  let cA: class A
  let vy: setvar y

  disjoint F x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- E* x F ~~> x

  proof
    cF
    vx
    cv
    #
    cli
    wbr
    #
    vx
    wmo
    @1
    vx
    wex
    #
    @1
    vx
    weu
    #
    wi
    @2
    cF
    vy
    cv
    #
    cli
    wbr
    #
    vy
    wex
    @3
    @1
    @5
    vx
    vy
    @0
    @4
    cF
    cli
    breq2
    cbvexv
    @5
    @3
    vy
    vx
    @4
    cF
    climeu
    exlimiv
    sylbi
    @1
    vx
    df-mo
    mpbir
end
