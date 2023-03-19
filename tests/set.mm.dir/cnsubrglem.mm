include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "c1.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "cnsubglem.mm"
include "rgen2a.mm"
include "crg.mm"
include "w3a.mm"
include "wb.mm"
include "cnring.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cnfld1.mm"
include "cnfldmul.mm"
include "issubrg2.mm"
include "ax-mp.mm"
include "mpbir3an.mm"

theorem cnsubrglem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnsubglem.1: |- ( x e. A -> x e. CC )
  assume cnsubglem.2: |- ( ( x e. A /\ y e. A ) -> ( x + y ) e. A )
  assume cnsubglem.3: |- ( x e. A -> -u x e. A )
  assume cnsubrglem.4: |- 1 e. A
  assume cnsubrglem.5: |- ( ( x e. A /\ y e. A ) -> ( x x. y ) e. A )

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- A e. ( SubRing ` CCfld )

  proof
    cA
    ccnfld
    csubrg
    cfv
    wcel
    #
    cA
    ccnfld
    csubg
    cfv
    wcel
    #
    c1
    cA
    wcel
    #
    vx
    cv
    vy
    cv
    cmul
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
    vy
    cA
    c1
    cnsubglem.1
    cnsubglem.2
    cnsubglem.3
    cnsubrglem.4
    cnsubglem
    cnsubrglem.4
    @3
    vx
    vy
    cA
    cnsubrglem.5
    rgen2a
    ccnfld
    crg
    wcel
    @0
    @1
    @2
    @4
    w3a
    wb
    cnring
    vx
    vy
    cA
    cc
    ccnfld
    cmul
    c1
    cnfldbas
    cnfld1
    cnfldmul
    issubrg2
    ax-mp
    mpbir3an
end
