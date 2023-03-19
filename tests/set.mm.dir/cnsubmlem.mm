include "ccnfld.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cc0.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "ssriv.mm"
include "rgen2a.mm"
include "crg.mm"
include "cmnd.mm"
include "w3a.mm"
include "wb.mm"
include "cnring.mm"
include "ringmnd.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldadd.mm"
include "issubm.mm"
include "mp2b.mm"
include "mpbir3an.mm"

theorem cnsubmlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnsubglem.1: |- ( x e. A -> x e. CC )
  assume cnsubglem.2: |- ( ( x e. A /\ y e. A ) -> ( x + y ) e. A )
  assume cnsubmlem.3: |- 0 e. A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- A e. ( SubMnd ` CCfld )

  proof
    cA
    ccnfld
    csubmnd
    cfv
    wcel
    #
    cA
    cc
    wss
    #
    cc0
    cA
    wcel
    #
    vx
    cv
    vy
    cv
    caddc
    co
    cA
    wcel
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    vx
    cA
    cc
    cnsubglem.1
    ssriv
    cnsubmlem.3
    @3
    vx
    vy
    cA
    cnsubglem.2
    rgen2a
    ccnfld
    crg
    wcel
    ccnfld
    cmnd
    wcel
    @0
    @1
    @2
    @4
    w3a
    wb
    cnring
    ccnfld
    ringmnd
    vx
    vy
    cc
    caddc
    cA
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cnfldadd
    issubm
    mp2b
    mpbir3an
end
