include "cv.mm"
include "wcel.mm"
include "bj-nfcrii.mm"
include "nf5i.mm"

theorem bj-nfcri
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume bj-nfcri.1: |- F/_ x A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- F/ x y e. A

  proof
    vy
    cv
    cA
    wcel
    vx
    vx
    vy
    cA
    bj-nfcri.1
    bj-nfcrii
    nf5i
end
