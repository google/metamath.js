include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "weq.mm"
include "nfv.mm"
include "eleq1.mm"
include "nfbidf.mm"
include "cbvalv.mm"

theorem nfcjust
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A. y F/ x y e. A <-> A. z F/ x z e. A )

  proof
    vy
    cv
    #
    cA
    wcel
    #
    vx
    wnf
    vz
    cv
    #
    cA
    wcel
    #
    vx
    wnf
    vy
    vz
    vy
    vz
    weq
    #
    @1
    @3
    vx
    @4
    vx
    nfv
    @0
    @2
    cA
    eleq1
    nfbidf
    cbvalv
end
