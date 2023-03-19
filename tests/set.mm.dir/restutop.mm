include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cutop.mm"
include "crest.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "simpl.mm"
include "cin.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "fvexd.mm"
include "elfvex.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "inss2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "syl.mm"
include "simp-5l.mm"
include "ad2antrr.mm"
include "ad6antr.mm"
include "xpexg.mm"
include "simplr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "inss1.mm"
include "imass1.mm"
include "ax-mp.mm"
include "sstr.mm"
include "mpan.mm"
include "crn.mm"
include "imassrn.mm"
include "rnin.mm"
include "sstri.mm"
include "rnxpid.mm"
include "sseqtri.mm"
include "a1i.mm"
include "ssind.mm"
include "adantl.mm"
include "simpllr.mm"
include "sseqtr4d.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "elutop.mm"
include "simplbda.mm"
include "r19.21bi.mm"
include "syl21anc.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "trust.mm"
include "biimpar.mm"
include "syl12anc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem restutop
  let cA: class A
  let cU: class U
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( U e. ( UnifOn ` X ) /\ A C_ X ) -> ( ( unifTop ` U ) |`t A ) C_ ( unifTop ` ( U |`t ( A X. A ) ) ) )

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
    wa
    #
    vb
    cU
    cutop
    cfv
    #
    cA
    crest
    co
    #
    cU
    cA
    cA
    cxp
    #
    crest
    co
    #
    cutop
    cfv
    #
    @3
    vb
    cv
    #
    @5
    wcel
    #
    @9
    @8
    wcel
    #
    @3
    @10
    wa
    #
    @3
    @9
    cA
    wss
    #
    vv
    cv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    @9
    wss
    #
    vv
    @7
    wrex
    #
    vx
    @9
    wral
    #
    @11
    @3
    @10
    simpl
    @12
    @9
    va
    cv
    #
    cA
    cin
    #
    wceq
    #
    va
    @4
    wrex
    #
    @13
    @3
    @10
    @24
    @3
    @4
    cvv
    wcel
    cA
    cvv
    wcel
    #
    @10
    @24
    wb
    @3
    cU
    cutop
    fvexd
    @3
    cA
    cX
    cvv
    @1
    cX
    cvv
    wcel
    @2
    cU
    cX
    cust
    elfvex
    adantr
    @1
    @2
    simpr
    ssexd
    #
    va
    @9
    cA
    @4
    cvv
    cvv
    elrest
    syl2anc
    biimpa
    #
    @23
    @13
    va
    @4
    @23
    @13
    @22
    cA
    wss
    @21
    cA
    inss2
    @9
    @22
    cA
    sseq1
    mpbiri
    rexlimivw
    syl
    @12
    @19
    vx
    @9
    @12
    @15
    @9
    wcel
    #
    wa
    #
    @23
    @19
    va
    @4
    @29
    @21
    @4
    wcel
    #
    wa
    #
    @23
    wa
    #
    vu
    cv
    #
    @16
    cima
    #
    @21
    wss
    #
    @19
    vu
    cU
    @32
    @33
    cU
    wcel
    #
    wa
    #
    @35
    wa
    #
    @33
    @6
    cin
    #
    @7
    wcel
    #
    @39
    @16
    cima
    #
    @9
    wss
    #
    @19
    @38
    @1
    @6
    cvv
    wcel
    #
    @36
    @40
    @32
    @1
    @36
    @35
    @1
    @2
    @10
    @28
    @30
    @23
    simp-5l
    #
    ad2antrr
    @38
    @25
    @25
    @43
    @3
    @25
    @10
    @28
    @30
    @23
    @36
    @35
    @26
    ad6antr
    #
    @45
    cA
    cA
    cvv
    cvv
    xpexg
    syl2anc
    @32
    @36
    @35
    simplr
    @33
    @6
    cU
    @0
    cvv
    elrestr
    syl3anc
    @38
    @41
    @22
    @9
    @35
    @41
    @22
    wss
    @37
    @35
    @41
    @21
    cA
    @41
    @34
    wss
    #
    @35
    @41
    @21
    wss
    @39
    @33
    wss
    @46
    @33
    @6
    inss1
    @39
    @33
    @16
    imass1
    ax-mp
    @41
    @34
    @21
    sstr
    mpan
    @41
    cA
    wss
    @35
    @41
    @6
    crn
    #
    cA
    @41
    @33
    crn
    #
    @47
    cin
    #
    @47
    @41
    @39
    crn
    @49
    @39
    @16
    imassrn
    @33
    @6
    rnin
    sstri
    @48
    @47
    inss2
    sstri
    cA
    rnxpid
    sseqtri
    a1i
    ssind
    adantl
    @31
    @23
    @36
    @35
    simpllr
    sseqtr4d
    @18
    @42
    vv
    @39
    @7
    @14
    @39
    wceq
    @17
    @41
    @9
    @14
    @39
    @16
    imaeq1
    sseq1d
    rspcev
    syl2anc
    @32
    @1
    @30
    @15
    @21
    wcel
    @35
    vu
    cU
    wrex
    #
    @44
    @29
    @30
    @23
    simplr
    @32
    @22
    @21
    @15
    @21
    cA
    inss1
    @32
    @15
    @9
    @22
    @12
    @28
    @30
    @23
    simpllr
    @31
    @23
    simpr
    eleqtrd
    sseldi
    @1
    @30
    wa
    @50
    vx
    @21
    @1
    @30
    @21
    cX
    wss
    @50
    vx
    @21
    wral
    vx
    vu
    @21
    cU
    cX
    elutop
    simplbda
    r19.21bi
    syl21anc
    r19.29a
    @12
    @24
    @28
    @27
    adantr
    r19.29a
    ralrimiva
    @3
    @11
    @13
    @20
    wa
    #
    @3
    @7
    cA
    cust
    cfv
    wcel
    @11
    @51
    wb
    cA
    cU
    cX
    trust
    vx
    vv
    @9
    @7
    cA
    elutop
    syl
    biimpar
    syl12anc
    ex
    ssrdv
end
