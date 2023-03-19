include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "ccfilu.mm"
include "c0.mm"
include "crest.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "wss.mm"
include "w3a.mm"
include "cxp.mm"
include "cfbas.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "simp1.mm"
include "simp2l.mm"
include "iscfilu.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "simpld.mm"
include "simp3.mm"
include "simp2r.mm"
include "trfbas2.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "cin.mm"
include "wceq.mm"
include "cvv.mm"
include "ad5antr.mm"
include "adantr.mm"
include "elfvexd.mm"
include "ssexd.mm"
include "ad4antr.mm"
include "simplr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "inxp.mm"
include "simpr.mm"
include "ssrin.mm"
include "syl.mm"
include "simpllr.mm"
include "sseqtr4d.mm"
include "syl5eqssr.mm"
include "id.mm"
include "sqxpeqd.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "3ad2antr2.mm"
include "3anassrs.mm"
include "r19.29a.mm"
include "xpexg.mm"
include "elrest.mm"
include "ralrimiva.mm"
include "wb.mm"
include "trust.mm"
include "mpbir2and.mm"

theorem trcfilu
  let cA: class A
  let cU: class U
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( U e. ( UnifOn ` X ) /\ ( F e. ( CauFilU ` U ) /\ -. (/) e. ( F |`t A ) ) /\ A C_ X ) -> ( F |`t A ) e. ( CauFilU ` ( U |`t ( A X. A ) ) ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cF
    cU
    ccfilu
    cfv
    #
    wcel
    #
    c0
    cF
    cA
    crest
    co
    #
    wcel
    wn
    #
    wa
    #
    cA
    cX
    wss
    #
    w3a
    #
    @4
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
    @4
    cA
    cfbas
    cfv
    wcel
    #
    vb
    cv
    #
    @13
    cxp
    #
    vw
    cv
    #
    wss
    #
    vb
    @4
    wrex
    #
    vw
    @10
    wral
    #
    @8
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @7
    @5
    @12
    @8
    @19
    va
    cv
    #
    @20
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
    @8
    @1
    @3
    @19
    @25
    wa
    #
    @1
    @6
    @7
    simp1
    #
    @1
    @3
    @5
    @7
    simp2l
    #
    @1
    @3
    @26
    vv
    cU
    cF
    cX
    va
    iscfilu
    biimpa
    syl2anc
    #
    simpld
    @1
    @6
    @7
    simp3
    #
    @1
    @3
    @5
    @7
    simp2r
    @19
    @7
    wa
    @12
    @5
    cA
    cF
    cX
    trfbas2
    biimpar
    syl21anc
    @8
    @17
    vw
    @10
    @8
    @15
    @10
    wcel
    #
    wa
    #
    @15
    @22
    @9
    cin
    #
    wceq
    #
    @17
    vv
    cU
    @32
    @22
    cU
    wcel
    #
    wa
    #
    @34
    wa
    #
    @23
    @17
    va
    cF
    @37
    @20
    cF
    wcel
    #
    wa
    #
    @23
    wa
    #
    @20
    cA
    cin
    #
    @4
    wcel
    #
    @41
    @41
    cxp
    #
    @15
    wss
    #
    @17
    @40
    @3
    cA
    cvv
    wcel
    #
    @38
    @42
    @8
    @3
    @31
    @35
    @34
    @38
    @23
    @28
    ad5antr
    @32
    @45
    @35
    @34
    @38
    @23
    @32
    cA
    cX
    cvv
    @32
    cU
    cust
    cX
    @8
    @1
    @31
    @27
    adantr
    #
    elfvexd
    @8
    @7
    @31
    @30
    adantr
    ssexd
    #
    ad4antr
    @37
    @38
    @23
    simplr
    @20
    cA
    cF
    @2
    cvv
    elrestr
    syl3anc
    @40
    @43
    @21
    @9
    cin
    #
    @15
    @20
    @20
    cA
    cA
    inxp
    @40
    @48
    @33
    @15
    @40
    @23
    @48
    @33
    wss
    @39
    @23
    simpr
    @21
    @22
    @9
    ssrin
    syl
    @36
    @34
    @38
    @23
    simpllr
    sseqtr4d
    syl5eqssr
    @16
    @44
    vb
    @41
    @4
    @13
    @41
    wceq
    #
    @14
    @43
    @15
    @49
    @13
    @41
    @49
    id
    sqxpeqd
    sseq1d
    rspcev
    syl2anc
    @8
    @31
    @35
    @34
    @24
    @8
    @31
    @35
    @24
    @34
    @8
    @24
    vv
    cU
    @8
    @19
    @25
    @29
    simprd
    r19.21bi
    3ad2antr2
    3anassrs
    r19.29a
    @32
    @1
    @9
    cvv
    wcel
    #
    @31
    @34
    vv
    cU
    wrex
    #
    @46
    @32
    @45
    @45
    @50
    @47
    @47
    cA
    cA
    cvv
    cvv
    xpexg
    syl2anc
    @8
    @31
    simpr
    @1
    @50
    wa
    @31
    @51
    vv
    @15
    @9
    cU
    @0
    cvv
    elrest
    biimpa
    syl21anc
    r19.29a
    ralrimiva
    @8
    @10
    cA
    cust
    cfv
    wcel
    #
    @11
    @12
    @18
    wa
    wb
    @8
    @1
    @7
    @52
    @27
    @30
    cA
    cU
    cX
    trust
    syl2anc
    vw
    @10
    @4
    cA
    vb
    iscfilu
    syl
    mpbir2and
end
