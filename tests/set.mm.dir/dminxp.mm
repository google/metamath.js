include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "wceq.mm"
include "ccnv.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "dfdm4.mm"
include "cnvin.mm"
include "cnvxp.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "rneqi.mm"
include "eqeq1i.mm"
include "rninxp.mm"
include "vex.mm"
include "brcnv.mm"
include "rexbii.mm"
include "ralbii.mm"
include "3bitri.mm"

theorem dminxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( dom ( C i^i ( A X. B ) ) = A <-> A. x e. A E. y e. B x C y )

  proof
    cC
    cA
    cB
    cxp
    #
    cin
    #
    cdm
    #
    cA
    wceq
    cC
    ccnv
    #
    cB
    cA
    cxp
    #
    cin
    #
    crn
    #
    cA
    wceq
    vy
    cv
    #
    vx
    cv
    #
    @3
    wbr
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @8
    @7
    cC
    wbr
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @2
    @6
    cA
    @2
    @1
    ccnv
    #
    crn
    @6
    @1
    dfdm4
    @13
    @5
    @13
    @3
    @0
    ccnv
    #
    cin
    @5
    cC
    @0
    cnvin
    @14
    @4
    @3
    cA
    cB
    cnvxp
    ineq2i
    eqtri
    rneqi
    eqtri
    eqeq1i
    vy
    vx
    cB
    cA
    @3
    rninxp
    @10
    @12
    vx
    cA
    @9
    @11
    vy
    cB
    @7
    @8
    cC
    vy
    vex
    vx
    vex
    brcnv
    rexbii
    ralbii
    3bitri
end
