include "cv.mm"
include "wss.mm"
include "cdif.mm"
include "cvv.mm"
include "vex.mm"
include "difexi.mm"
include "sseq1.mm"
include "ssdifss.mm"
include "adantr.mm"
include "cllem0.mm"

theorem ssdifcl
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
  assert |- A. x e. A A. y e. A ( x \ y ) e. A

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
    cdif
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
    difexi
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
    cB
    @2
    ssdifss
    adantr
    cllem0
end
