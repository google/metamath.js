include "cv.mm"
include "wss.mm"
include "cab.mm"
include "sseq1.mm"
include "cbvabv.mm"
include "eqtri.mm"

theorem pwjust
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- { x | x C_ A } = { y | y C_ A }

  proof
    vx
    cv
    #
    cA
    wss
    #
    vx
    cab
    vz
    cv
    #
    cA
    wss
    #
    vz
    cab
    vy
    cv
    #
    cA
    wss
    #
    vy
    cab
    @1
    @3
    vx
    vz
    @0
    @2
    cA
    sseq1
    cbvabv
    @3
    @5
    vz
    vy
    @2
    @4
    cA
    sseq1
    cbvabv
    eqtri
end
