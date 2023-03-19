include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-elisset.mm"
include "ax-mp.mm"

theorem bj-isseti
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-isseti.1: |- A e. V

  disjoint A x
  assert |- E. x x = A

  proof
    cA
    cV
    wcel
    vx
    cv
    cA
    wceq
    vx
    wex
    bj-isseti.1
    vx
    cA
    cV
    bj-elisset
    ax-mp
end
