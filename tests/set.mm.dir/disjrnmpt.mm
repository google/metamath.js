include "wdisj.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "disjabrex.mm"
include "wb.mm"
include "eqid.mm"
include "rnmpt.mm"
include "disjeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem disjrnmpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( Disj_ x e. A B -> Disj_ y e. ran ( x e. A |-> B ) y )

  proof
    vx
    cA
    cB
    wdisj
    vy
    vz
    cv
    cB
    wceq
    vx
    cA
    wrex
    vz
    cab
    #
    vy
    cv
    #
    wdisj
    #
    vy
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    @1
    wdisj
    #
    vx
    vy
    vz
    cA
    cB
    disjabrex
    @4
    @0
    wceq
    @5
    @2
    wb
    vx
    vz
    cA
    cB
    @3
    @3
    eqid
    rnmpt
    vy
    @4
    @0
    @1
    disjeq1
    ax-mp
    sylibr
end
