include "cv.mm"
include "wss.mm"
include "cun.mm"
include "cvv.mm"
include "vex.mm"
include "unex.mm"
include "sseq1.mm"
include "wa.mm"
include "unss.mm"
include "biimpi.mm"
include "cllem0.mm"

theorem ssuncl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume ssficl.a: |- A = { z | z C_ B }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint B z
  assert |- A. x e. A A. y e. A ( x u. y ) e. A

  proof
    vz
    cv
    #
    cB
    wss
    vx
    cv
    #
    vy
    cv
    #
    cun
    #
    cB
    wss
    #
    @1
    cB
    wss
    #
    @2
    cB
    wss
    #
    vx
    vy
    vz
    @3
    cvv
    cA
    ssficl.a
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
    sseq1
    @0
    @1
    cB
    sseq1
    @0
    @2
    cB
    sseq1
    @5
    @6
    wa
    @4
    @1
    @2
    cB
    unss
    biimpi
    cllem0
end
