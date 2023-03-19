include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "eq0.mm"
include "mpgbir.mm"

theorem nel0
  let vx: setvar x
  let cA: class A
  assume nel0.1: |- -. x e. A

  disjoint A x
  assert |- A = (/)

  proof
    cA
    c0
    wceq
    vx
    cv
    cA
    wcel
    wn
    vx
    vx
    cA
    eq0
    nel0.1
    mpgbir
end
