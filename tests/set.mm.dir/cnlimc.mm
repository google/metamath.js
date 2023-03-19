include "cc.mm"
include "wss.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "wa.mm"
include "climc.mm"
include "wceq.mm"
include "ssid.mm"
include "eqid.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mpan2.mm"
include "eleq2d.mm"
include "wb.mm"
include "resttopon.mm"
include "mpan.mm"
include "cncnp.mm"
include "sylancl.mm"
include "cnplimc.mm"
include "baibd.mm"
include "an32s.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "3bitrd.mm"

theorem cnlimc
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint A x
  disjoint F x
  assert |- ( A C_ CC -> ( F e. ( A -cn-> CC ) <-> ( F : A --> CC /\ A. x e. A ( F ` x ) e. ( F limCC x ) ) ) )

  proof
    cA
    cc
    wss
    #
    cF
    cA
    cc
    ccncf
    co
    #
    wcel
    cF
    ccnfld
    ctopn
    cfv
    #
    cA
    crest
    co
    #
    @2
    ccn
    co
    #
    wcel
    #
    cA
    cc
    cF
    wf
    #
    cF
    vx
    cv
    #
    @3
    @2
    ccnp
    co
    cfv
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @6
    @7
    cF
    cfv
    cF
    @7
    climc
    co
    wcel
    #
    vx
    cA
    wral
    #
    wa
    @0
    @1
    @4
    cF
    @0
    cc
    cc
    wss
    @1
    @4
    wceq
    cc
    ssid
    cA
    cc
    @2
    @3
    @2
    @2
    eqid
    #
    @3
    eqid
    #
    @2
    cc
    crest
    co
    #
    @2
    @2
    cc
    ctopon
    cfv
    #
    wcel
    #
    @15
    @2
    wceq
    @2
    @13
    cnfldtopon
    #
    @2
    @16
    cc
    cc
    @2
    @18
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mpan2
    eleq2d
    @0
    @3
    cA
    ctopon
    cfv
    wcel
    #
    @17
    @5
    @10
    wb
    @17
    @0
    @19
    @18
    cA
    @2
    cc
    resttopon
    mpan
    @18
    vx
    cF
    @3
    @2
    cA
    cc
    cncnp
    sylancl
    @0
    @6
    @9
    @12
    @0
    @6
    wa
    @8
    @11
    vx
    cA
    @0
    @7
    cA
    wcel
    #
    @6
    @8
    @11
    wb
    @0
    @20
    wa
    @8
    @6
    @11
    cA
    @7
    cF
    @3
    @2
    @13
    @14
    cnplimc
    baibd
    an32s
    ralbidva
    pm5.32da
    3bitrd
end
