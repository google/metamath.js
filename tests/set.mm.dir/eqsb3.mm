include "cv.mm"
include "wceq.mm"
include "wsb.mm"
include "eqsb3lem.mm"
include "sbbii.mm"
include "nfv.mm"
include "sbco2.mm"
include "3bitr3i.mm"

theorem eqsb3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w

  disjoint A y
  disjoint w y
  disjoint A w
  disjoint w x
  assert |- ( [ x / y ] y = A <-> x = A )

  proof
    vy
    cv
    cA
    wceq
    #
    vy
    vw
    wsb
    #
    vw
    vx
    wsb
    vw
    cv
    cA
    wceq
    #
    vw
    vx
    wsb
    @0
    vy
    vx
    wsb
    vx
    cv
    cA
    wceq
    @1
    @2
    vw
    vx
    vw
    vy
    cA
    eqsb3lem
    sbbii
    @0
    vy
    vx
    vw
    @0
    vw
    nfv
    sbco2
    vx
    vw
    cA
    eqsb3lem
    3bitr3i
end
