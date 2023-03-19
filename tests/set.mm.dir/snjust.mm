include "cv.mm"
include "wceq.mm"
include "cab.mm"
include "eqeq1.mm"
include "cbvabv.mm"
include "eqtri.mm"

theorem snjust
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- { x | x = A } = { y | y = A }

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    cab
    vz
    cv
    #
    cA
    wceq
    #
    vz
    cab
    vy
    cv
    #
    cA
    wceq
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
    eqeq1
    cbvabv
    @3
    @5
    vz
    vy
    @2
    @4
    cA
    eqeq1
    cbvabv
    eqtri
end
