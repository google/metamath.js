include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "cab.mm"
include "weq.mm"
include "eleq1.mm"
include "orbi12d.mm"
include "cbvabv.mm"
include "eqtri.mm"

theorem unjust
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- { x | ( x e. A \/ x e. B ) } = { y | ( y e. A \/ y e. B ) }

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wo
    #
    vx
    cab
    vz
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wo
    #
    vz
    cab
    vy
    cv
    #
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wo
    #
    vy
    cab
    @3
    @7
    vx
    vz
    vx
    vz
    weq
    @1
    @5
    @2
    @6
    @0
    @4
    cA
    eleq1
    @0
    @4
    cB
    eleq1
    orbi12d
    cbvabv
    @7
    @11
    vz
    vy
    vz
    vy
    weq
    @5
    @9
    @6
    @10
    @4
    @8
    cA
    eleq1
    @4
    @8
    cB
    eleq1
    orbi12d
    cbvabv
    eqtri
end
