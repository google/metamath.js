include "cv.mm"
include "wcel.mm"
include "wnfc.mm"
include "wnf.mm"
include "nfcr.mm"
include "ax-mp.mm"
include "nf5ri.mm"
include "hblem.mm"

theorem nfcrii
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume nfcri.1: |- F/_ x A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( y e. A -> A. x y e. A )

  proof
    vx
    vz
    vy
    cA
    vz
    cv
    cA
    wcel
    #
    vx
    vx
    cA
    wnfc
    @0
    vx
    wnf
    nfcri.1
    vx
    vz
    cA
    nfcr
    ax-mp
    nf5ri
    hblem
end
