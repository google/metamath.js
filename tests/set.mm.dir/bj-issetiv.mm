include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "bj-elissetv.mm"
include "ax-mp.mm"

theorem bj-issetiv
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bj-issetiv.1: |- A e. V

  disjoint A x
  disjoint V x
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
    bj-issetiv.1
    vx
    cA
    cV
    bj-elissetv
    ax-mp
end
