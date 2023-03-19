include "cv.mm"
include "wss.mm"
include "cin.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "sseq1.mm"
include "ssinss1.mm"
include "adantr.mm"
include "cllem0.mm"

theorem ssficl
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
  assert |- A. x e. A A. y e. A ( x i^i y ) e. A

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
    cin
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
    inex1
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
    @4
    @6
    @1
    @2
    cB
    ssinss1
    adantr
    cllem0
end
