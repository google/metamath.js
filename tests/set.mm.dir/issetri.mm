include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isset.mm"
include "mpbir.mm"

theorem issetri
  let vx: setvar x
  let cA: class A
  assume issetri.1: |- E. x x = A

  disjoint A x
  assert |- A e. _V

  proof
    cA
    cvv
    wcel
    vx
    cv
    cA
    wceq
    vx
    wex
    issetri.1
    vx
    cA
    isset
    mpbir
end
