include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "wf1o.mm"
include "wex.mm"
include "numth2.mm"
include "bren.mm"
include "rexbii.mm"
include "mpbi.mm"

theorem numth
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  assume numth.1: |- A e. _V

  disjoint f x
  disjoint A f
  disjoint A x
  assert |- E. x e. On E. f f : x -1-1-onto-> A

  proof
    vx
    cv
    #
    cA
    cen
    wbr
    #
    vx
    con0
    wrex
    @0
    cA
    vf
    cv
    wf1o
    vf
    wex
    #
    vx
    con0
    wrex
    vx
    cA
    numth.1
    numth2
    @1
    @2
    vx
    con0
    @0
    cA
    vf
    bren
    rexbii
    mpbi
end
