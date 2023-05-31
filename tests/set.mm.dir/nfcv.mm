include "cv.mm"
include "wcel.mm"
include "nfv.mm"
include "nfci.mm"

theorem nfcv
  param vx: setvar x
  param cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- F/_ x A

  proof
    vx
    vy
    cA
    vy
    cv
    cA
    wcel
    vx
    nfv
    nfci
end
