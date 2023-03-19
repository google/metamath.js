include "cv.mm"
include "wss.mm"
include "cun.mm"
include "cvv.mm"
include "vex.mm"
include "unex.mm"
include "sseq2.mm"
include "ssun3.mm"
include "adantr.mm"
include "cllem0.mm"

theorem superuncl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume superficl.a: |- A = { z | B C_ z }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint B z
  assert |- A. x e. A A. y e. A ( x u. y ) e. A

  proof
    cB
    vz
    cv
    #
    wss
    cB
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    wss
    #
    cB
    @1
    wss
    #
    cB
    @2
    wss
    #
    vx
    vy
    vz
    @3
    cvv
    cA
    superficl.a
    @1
    @2
    vx
    vex
    vy
    vex
    unex
    @0
    @3
    cB
    sseq2
    @0
    @1
    cB
    sseq2
    @0
    @2
    cB
    sseq2
    @5
    @4
    @6
    cB
    @1
    @2
    ssun3
    adantr
    cllem0
end
