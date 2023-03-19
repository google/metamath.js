include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cab.mm"
include "weq.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "cbvabv.mm"
include "eqtri.mm"

theorem difjust
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
  assert |- { x | ( x e. A /\ -. x e. B ) } = { y | ( y e. A /\ -. y e. B ) }

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
    wn
    #
    wa
    #
    vx
    cab
    vz
    cv
    #
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wn
    #
    wa
    #
    vz
    cab
    vy
    cv
    #
    cA
    wcel
    #
    @10
    cB
    wcel
    #
    wn
    #
    wa
    #
    vy
    cab
    @4
    @9
    vx
    vz
    vx
    vz
    weq
    #
    @1
    @6
    @3
    @8
    @0
    @5
    cA
    eleq1
    @15
    @2
    @7
    @0
    @5
    cB
    eleq1
    notbid
    anbi12d
    cbvabv
    @9
    @14
    vz
    vy
    vz
    vy
    weq
    #
    @6
    @11
    @8
    @13
    @5
    @10
    cA
    eleq1
    @16
    @7
    @12
    @5
    @10
    cB
    eleq1
    notbid
    anbi12d
    cbvabv
    eqtri
end
