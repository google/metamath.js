include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-clel.mm"
include "vex.mm"
include "biantru.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem isset
  param vx: setvar x
  param cA: class A

  disjoint A x
  assert |- ( A e. _V <-> E. x x = A )

  proof
    cA
    cvv
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cvv
    wcel
    #
    wa
    #
    vx
    wex
    @1
    vx
    wex
    vx
    cA
    cvv
    df-clel
    @1
    @3
    vx
    @2
    @1
    vx
    vex
    biantru
    exbii
    bitr4i
end
