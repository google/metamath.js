include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "mpbi.mm"

theorem bj-n0i
  let vx: setvar x
  let cA: class A
  assume bj-n0i.1: |- A =/= (/)

  disjoint A x
  assert |- E. x x e. A

  proof
    cA
    c0
    wne
    vx
    cv
    cA
    wcel
    vx
    wex
    bj-n0i.1
    vx
    cA
    n0
    mpbi
end
