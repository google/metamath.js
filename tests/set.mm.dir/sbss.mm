include "cv.mm"
include "wss.mm"
include "wsb.mm"
include "vex.mm"
include "sbequ.mm"
include "sseq1.mm"
include "nfv.mm"
include "sbie.mm"
include "vtoclb.mm"

theorem sbss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint y z
  disjoint x z
  disjoint A z
  assert |- ( [ y / x ] x C_ A <-> y C_ A )

  proof
    vx
    cv
    #
    cA
    wss
    #
    vx
    vz
    wsb
    vz
    cv
    #
    cA
    wss
    #
    @1
    vx
    vy
    wsb
    vy
    cv
    #
    cA
    wss
    vz
    @4
    vy
    vex
    @1
    vz
    vy
    vx
    sbequ
    @2
    @4
    cA
    sseq1
    @1
    @3
    vx
    vz
    @3
    vx
    nfv
    @0
    @2
    cA
    sseq1
    sbie
    vtoclb
end
