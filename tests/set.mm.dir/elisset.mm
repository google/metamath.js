include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elex.mm"
include "isset.mm"
include "sylib.mm"

theorem elisset
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  assert |- ( A e. V -> E. x x = A )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    vx
    cv
    cA
    wceq
    vx
    wex
    cA
    cV
    elex
    vx
    cA
    isset
    sylib
end
