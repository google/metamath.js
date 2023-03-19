include "cv.mm"
include "wcel.mm"
include "nf5i.mm"
include "nfci.mm"

theorem nfcii
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfcii.1: |- ( y e. A -> A. x y e. A )

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
    nfcii.1
    nf5i
    nfci
end
