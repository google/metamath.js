include "cc.mm"
include "cv.mm"
include "ccxp.mm"
include "co.mm"
include "cmpt2.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "ctx.mm"
include "ccn.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "crp.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "adantr.mm"
include "cc0.mm"
include "wne.mm"
include "logdmn0.mm"
include "simpr.mm"
include "cxpefd.mm"
include "mpt2eq3ia.mm"
include "wtru.mm"
include "crest.mm"
include "ctopon.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "ssriv.mm"
include "resttopon.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "cnmpt2nd.mm"
include "cres.mm"
include "wceq.mm"
include "fvres.mm"
include "cnmpt1st.mm"
include "ccncf.mm"
include "logcn.mm"
include "ssid.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "mp2an.mm"
include "eleqtri.mm"
include "cnmpt21f.mm"
include "syl5eqelr.mm"
include "mulcn.mm"
include "cnmpt22f.mm"
include "efcn.mm"
include "cncfcn1.mm"
include "trud.mm"
include "eqeltri.mm"

theorem cxpcn
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cJ: class J
  let cK: class K
  assume cxpcn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume cxpcn.j: |- J = ( TopOpen ` CCfld )
  assume cxpcn.k: |- K = ( J |`t D )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  assert |- ( x e. D , y e. CC |-> ( x ^c y ) ) e. ( ( K tX J ) Cn J )

  proof
    vx
    vy
    cD
    cc
    vx
    cv
    #
    vy
    cv
    #
    ccxp
    co
    #
    cmpt2
    vx
    vy
    cD
    cc
    @1
    @0
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt2
    #
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    #
    vx
    vy
    cD
    cc
    @2
    @5
    @0
    cD
    wcel
    #
    @1
    cc
    wcel
    #
    wa
    @0
    @1
    @8
    @0
    cc
    wcel
    #
    @9
    @8
    @10
    @0
    cr
    wcel
    @0
    crp
    wcel
    wi
    @0
    cD
    cxpcn.d
    ellogdm
    simplbi
    #
    adantr
    @8
    @0
    cc0
    wne
    @9
    @0
    cD
    cxpcn.d
    logdmn0
    adantr
    @8
    @9
    simpr
    cxpefd
    mpt2eq3ia
    @6
    @7
    wcel
    wtru
    vx
    vy
    @4
    ce
    cK
    cJ
    cJ
    cJ
    cD
    cc
    wtru
    cK
    cJ
    cD
    crest
    co
    #
    cD
    ctopon
    cfv
    #
    cxpcn.k
    wtru
    cJ
    cc
    ctopon
    cfv
    #
    wcel
    #
    cD
    cc
    wss
    #
    @12
    @13
    wcel
    @15
    wtru
    cJ
    cxpcn.j
    cnfldtopon
    #
    a1i
    #
    vx
    cD
    cc
    @11
    ssriv
    #
    cD
    cJ
    cc
    resttopon
    sylancl
    syl5eqel
    #
    @18
    wtru
    vx
    vy
    @1
    @3
    cmul
    cK
    cJ
    cJ
    cJ
    cJ
    cD
    cc
    @20
    @18
    wtru
    vx
    vy
    cK
    cJ
    cD
    cc
    @20
    @18
    cnmpt2nd
    wtru
    vx
    vy
    cD
    cc
    @3
    cmpt2
    vx
    vy
    cD
    cc
    @0
    clog
    cD
    cres
    #
    cfv
    #
    cmpt2
    @7
    vx
    vy
    cD
    cc
    @22
    @3
    @8
    @22
    @3
    wceq
    @9
    @0
    cD
    clog
    fvres
    adantr
    mpt2eq3ia
    wtru
    vx
    vy
    @0
    @21
    cK
    cJ
    cK
    cJ
    cD
    cc
    @20
    @18
    wtru
    vx
    vy
    cK
    cJ
    cD
    cc
    @20
    @18
    cnmpt1st
    @21
    cK
    cJ
    ccn
    co
    #
    wcel
    wtru
    @21
    cD
    cc
    ccncf
    co
    #
    @23
    cD
    cxpcn.d
    logcn
    @16
    cc
    cc
    wss
    @24
    @23
    wceq
    @19
    cc
    ssid
    cD
    cc
    cJ
    cK
    cJ
    cxpcn.j
    cxpcn.k
    cJ
    cc
    crest
    co
    #
    cJ
    @15
    @25
    cJ
    wceq
    @17
    cJ
    @14
    cc
    cc
    cJ
    @17
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    mp2an
    eleqtri
    a1i
    cnmpt21f
    syl5eqelr
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wtru
    cJ
    cxpcn.j
    mulcn
    a1i
    cnmpt22f
    ce
    cJ
    cJ
    ccn
    co
    #
    wcel
    wtru
    ce
    cc
    cc
    ccncf
    co
    @26
    efcn
    cJ
    cxpcn.j
    cncfcn1
    eleqtri
    a1i
    cnmpt21f
    trud
    eqeltri
end
