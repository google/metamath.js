include "ccnfld.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "ssriv.mm"
include "ne0ii.mm"
include "ralrimiva.mm"
include "cneg.mm"
include "wceq.mm"
include "cnfldneg.mm"
include "syl.mm"
include "eqeltrd.mm"
include "jca.mm"
include "rgen.mm"
include "cgrp.mm"
include "w3a.mm"
include "wb.mm"
include "crg.mm"
include "cnring.mm"
include "ringgrp.mm"
include "ax-mp.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "eqid.mm"
include "issubg2.mm"
include "mpbir3an.mm"

theorem cnsubglem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume cnsubglem.1: |- ( x e. A -> x e. CC )
  assume cnsubglem.2: |- ( ( x e. A /\ y e. A ) -> ( x + y ) e. A )
  assume cnsubglem.3: |- ( x e. A -> -u x e. A )
  assume cnsubglem.4: |- B e. A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- A e. ( SubGrp ` CCfld )

  proof
    cA
    ccnfld
    csubg
    cfv
    wcel
    #
    cA
    cc
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
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
    #
    @3
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    wa
    #
    vx
    cA
    wral
    #
    vx
    cA
    cc
    cnsubglem.1
    ssriv
    cB
    cA
    cnsubglem.4
    ne0ii
    @9
    vx
    cA
    @3
    cA
    wcel
    #
    @5
    @8
    @11
    @4
    vy
    cA
    cnsubglem.2
    ralrimiva
    @11
    @7
    @3
    cneg
    #
    cA
    @11
    @3
    cc
    wcel
    @7
    @12
    wceq
    cnsubglem.1
    @3
    cnfldneg
    syl
    cnsubglem.3
    eqeltrd
    jca
    rgen
    ccnfld
    cgrp
    wcel
    #
    @0
    @1
    @2
    @10
    w3a
    wb
    ccnfld
    crg
    wcel
    @13
    cnring
    ccnfld
    ringgrp
    ax-mp
    vx
    vy
    cc
    caddc
    cA
    ccnfld
    @6
    cnfldbas
    cnfldadd
    @6
    eqid
    issubg2
    ax-mp
    mpbir3an
end
