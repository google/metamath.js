include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-clel.mm"
include "exsimpl.mm"
include "sylbi.mm"

theorem bj-elissetv
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  disjoint V x
  assert |- ( A e. V -> E. x x = A )

  proof
    cA
    cV
    wcel
    vx
    cv
    #
    cA
    wceq
    #
    @0
    cV
    wcel
    #
    wa
    vx
    wex
    @1
    vx
    wex
    vx
    cA
    cV
    df-clel
    @1
    @2
    vx
    exsimpl
    sylbi
end
