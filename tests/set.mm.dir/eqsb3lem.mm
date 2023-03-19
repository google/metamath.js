include "cv.mm"
include "wceq.mm"
include "nfv.mm"
include "eqeq1.mm"
include "sbie.mm"

theorem eqsb3lem
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A y
  assert |- ( [ x / y ] y = A <-> x = A )

  proof
    vy
    cv
    #
    cA
    wceq
    vx
    cv
    #
    cA
    wceq
    #
    vy
    vx
    @2
    vy
    nfv
    @0
    @1
    cA
    eqeq1
    sbie
end
