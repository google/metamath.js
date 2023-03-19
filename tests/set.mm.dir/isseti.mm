include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "isset.mm"
include "mpbi.mm"

theorem isseti
  let vx: setvar x
  let cA: class A
  assume isseti.1: |- A e. _V

  disjoint A x
  assert |- E. x x = A

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
    isseti.1
    vx
    cA
    isset
    mpbi
end
