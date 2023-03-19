include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "weq.mm"
include "nfv.mm"
include "eleq1w.mm"
include "nfbidf.mm"
include "bj-cbvalvv.mm"

theorem bj-nfcjust
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
    cA
    wcel
    #
    vx
    wnf
    vz
    cv
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
    @0
    @1
    vx
    @2
    vx
    nfv
    vy
    vz
    cA
    eleq1w
    nfbidf
    bj-cbvalvv
end
