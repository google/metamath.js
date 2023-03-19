include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cxp.mm"
include "crest.mm"
include "co.mm"
include "ccfilu.mm"
include "w3a.mm"
include "cfbas.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "cpw.mm"
include "cvv.mm"
include "wa.mm"
include "trust.mm"
include "iscfilu.mm"
include "biimpa.mm"
include "stoic3.mm"
include "simpld.mm"
include "fbsspw.mm"
include "syl.mm"
include "simp2.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "simp1.mm"
include "elfvexd.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "cin.mm"
include "adantr.mm"
include "ssexd.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simpr.mm"
include "elrestr.mm"
include "simprd.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "reximi.mm"
include "ralrimiva.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem cfiluweak
  let cA: class A
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vu: setvar u
  let vv: setvar v


  assert |- ( ( U e. ( UnifOn ` X ) /\ A C_ X /\ F e. ( CauFilU ` ( U |`t ( A X. A ) ) ) ) -> F e. ( CauFilU ` U ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cA
    cX
    wss
    #
    cF
    cU
    cA
    cA
    cxp
    #
    crest
    co
    #
    ccfilu
    cfv
    wcel
    #
    w3a
    #
    cF
    cU
    ccfilu
    cfv
    wcel
    #
    cF
    cX
    cfbas
    cfv
    wcel
    #
    va
    cv
    #
    @9
    cxp
    #
    vv
    cv
    #
    wss
    #
    va
    cF
    wrex
    #
    vv
    cU
    wral
    #
    @6
    cF
    cA
    cfbas
    cfv
    wcel
    #
    cF
    cX
    cpw
    #
    wss
    cX
    cvv
    wcel
    #
    @8
    @6
    @15
    @10
    vu
    cv
    #
    wss
    #
    va
    cF
    wrex
    #
    vu
    @4
    wral
    #
    @1
    @2
    @4
    cA
    cust
    cfv
    wcel
    #
    @5
    @15
    @21
    wa
    #
    cA
    cU
    cX
    trust
    @22
    @5
    @23
    vu
    @4
    cF
    cA
    va
    iscfilu
    biimpa
    stoic3
    #
    simpld
    #
    @6
    cF
    cA
    cpw
    #
    @16
    @6
    @15
    cF
    @26
    wss
    @25
    cA
    cF
    fbsspw
    syl
    @6
    @2
    @26
    @16
    wss
    @1
    @2
    @5
    simp2
    #
    cA
    cX
    sspwb
    sylib
    sstrd
    @6
    cU
    cust
    cX
    @1
    @2
    @5
    simp1
    #
    elfvexd
    #
    cF
    cvv
    cA
    cX
    fbasweak
    syl3anc
    @6
    @13
    vv
    cU
    @6
    @11
    cU
    wcel
    #
    wa
    #
    @10
    @11
    @3
    cin
    #
    wss
    #
    va
    cF
    wrex
    #
    @13
    @31
    @32
    @4
    wcel
    #
    @21
    @34
    @31
    @1
    @3
    cvv
    wcel
    #
    @30
    @35
    @6
    @1
    @30
    @28
    adantr
    @31
    cA
    cvv
    wcel
    #
    @37
    @36
    @31
    cA
    cX
    cvv
    @6
    @17
    @30
    @29
    adantr
    @6
    @2
    @30
    @27
    adantr
    ssexd
    #
    @38
    cA
    cA
    cvv
    cvv
    xpexg
    syl2anc
    @6
    @30
    simpr
    @11
    @3
    cU
    @0
    cvv
    elrestr
    syl3anc
    @6
    @21
    @30
    @6
    @15
    @21
    @24
    simprd
    adantr
    @20
    @34
    vu
    @32
    @4
    @18
    @32
    wceq
    @19
    @33
    va
    cF
    @18
    @32
    @10
    sseq2
    rexbidv
    rspcva
    syl2anc
    @33
    @12
    va
    cF
    @33
    @32
    @11
    wss
    @12
    @11
    @3
    inss1
    @10
    @32
    @11
    sstr
    mpan2
    reximi
    syl
    ralrimiva
    @1
    @2
    @7
    @8
    @14
    wa
    wb
    @5
    vv
    cU
    cF
    cX
    va
    iscfilu
    3ad2ant1
    mpbir2and
end
