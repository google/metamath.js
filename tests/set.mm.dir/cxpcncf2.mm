include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "ccxp.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccn.mm"
include "ccncf.mm"
include "crest.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "csn.mm"
include "wf.mm"
include "wss.mm"
include "difss.mm"
include "resttopon.mm"
include "mp2an.mm"
include "id.mm"
include "snidg.mm"
include "adantr.mm"
include "fmptd.mm"
include "cnconst.mm"
include "syl22anc.mm"
include "cnmptid.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cxpcn.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "wceq.mm"
include "ssid.mm"
include "cvv.mm"
include "elexi.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "eleqtrd.mm"

theorem cxpcncf2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k x
  assert |- ( A e. ( CC \ ( -oo (,] 0 ) ) -> ( x e. CC |-> ( A ^c x ) ) e. ( CC -cn-> CC ) )

  proof
    cA
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    wcel
    #
    vx
    cc
    cA
    vx
    cv
    #
    ccxp
    co
    #
    cmpt
    ccnfld
    ctopn
    cfv
    #
    @5
    ccn
    co
    #
    cc
    cc
    ccncf
    co
    #
    @2
    vx
    vy
    vz
    cA
    @3
    vy
    cv
    #
    vz
    cv
    #
    ccxp
    co
    #
    @4
    @5
    @5
    @1
    crest
    co
    #
    @5
    @5
    cc
    @1
    cc
    @5
    cc
    ctopon
    cfv
    #
    wcel
    #
    @2
    @5
    @5
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    @2
    @13
    @11
    @1
    ctopon
    cfv
    wcel
    #
    @2
    cc
    cA
    csn
    #
    vx
    cc
    cA
    cmpt
    #
    wf
    @19
    @5
    @11
    ccn
    co
    wcel
    @16
    @17
    @2
    @13
    @1
    cc
    wss
    @17
    @15
    cc
    @0
    difss
    @1
    @5
    cc
    resttopon
    mp2an
    a1i
    #
    @2
    id
    @2
    vx
    cc
    cA
    @18
    @19
    @2
    cA
    @18
    wcel
    @3
    cc
    wcel
    cA
    @1
    snidg
    adantr
    @19
    eqid
    fmptd
    cA
    @19
    @5
    @11
    cc
    @1
    cnconst
    syl22anc
    @2
    vx
    @5
    cc
    @16
    cnmptid
    @20
    @16
    vy
    vz
    @1
    cc
    @10
    cmpt2
    @11
    @5
    ctx
    co
    @5
    ccn
    co
    wcel
    @2
    vy
    vz
    @1
    @5
    @11
    @1
    eqid
    @14
    @11
    eqid
    cxpcn
    a1i
    @8
    cA
    @9
    @3
    ccxp
    oveq12
    cnmpt12
    @6
    @7
    wceq
    @2
    @7
    @6
    cc
    cc
    wss
    #
    @21
    @7
    @6
    wceq
    cc
    ssid
    #
    @22
    cc
    cc
    @5
    @5
    @5
    @14
    @5
    cc
    crest
    co
    #
    @5
    @5
    cvv
    wcel
    @23
    @5
    wceq
    @5
    @12
    @15
    elexi
    @5
    cvv
    cc
    cc
    @5
    @15
    toponunii
    restid
    ax-mp
    eqcomi
    #
    @24
    cncfcn
    mp2an
    eqcomi
    a1i
    eleqtrd
end
