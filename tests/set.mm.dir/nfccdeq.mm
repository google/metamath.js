include "cv.mm"
include "wcel.mm"
include "nfcri.mm"
include "weq.mm"
include "equid.mm"
include "cdeqth.mm"
include "cdeqel.mm"
include "nfcdeq.mm"
include "eqriv.mm"

theorem nfccdeq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfccdeq.1: |- F/_ x A
  assume nfccdeq.2: |- CondEq ( x = y -> A = B )

  disjoint B x
  disjoint A y
  disjoint x z
  disjoint B z
  disjoint y z
  disjoint A z
  assert |- A = B

  proof
    vz
    cA
    cB
    vz
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    vx
    vy
    vx
    vz
    cA
    nfccdeq.1
    nfcri
    vx
    vy
    @0
    @0
    cA
    cB
    vz
    vz
    weq
    vx
    vy
    vz
    equid
    cdeqth
    nfccdeq.2
    cdeqel
    nfcdeq
    eqriv
end
