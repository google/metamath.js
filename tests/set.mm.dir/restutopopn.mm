include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cutop.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "elutop.mm"
include "simprbda.mm"
include "restutop.mm"
include "syldan.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "trust.mm"
include "syl.mm"
include "adantr.mm"
include "sstrd.mm"
include "simp-9l.mm"
include "simplr.mm"
include "simp-4r.mm"
include "ustincl.mm"
include "syl3anc.mm"
include "inimass.mm"
include "ssrin.mm"
include "adantl.mm"
include "simpllr.mm"
include "imaeq1d.mm"
include "ad5antr.mm"
include "simp-5r.mm"
include "sseldd.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "vex.mm"
include "inimasn.mm"
include "ax-mp.mm"
include "xpimasn.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "incom.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "sseqtr4d.mm"
include "syl5ss.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "simp-4l.mm"
include "simplbda.mm"
include "r19.21bi.mm"
include "r19.29a.mm"
include "sqxpexg.mm"
include "elrest.mm"
include "sylan2.mm"
include "biimpa.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "fvex.mm"
include "mpan.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem restutopopn
  let cA: class A
  let cU: class U
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vv: setvar v


  assert |- ( ( U e. ( UnifOn ` X ) /\ A e. ( unifTop ` U ) ) -> ( ( unifTop ` U ) |`t A ) = ( unifTop ` ( U |`t ( A X. A ) ) ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cA
    cU
    cutop
    cfv
    #
    wcel
    #
    wa
    #
    @2
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
    @1
    @3
    cA
    cX
    wss
    #
    @5
    @8
    wss
    @1
    @3
    @9
    vt
    cv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    cA
    wss
    #
    vt
    cU
    wrex
    #
    vx
    cA
    wral
    #
    vx
    vt
    cA
    cU
    cX
    elutop
    #
    simprbda
    #
    cA
    cU
    cX
    restutop
    syldan
    @4
    vb
    @8
    @5
    @4
    vb
    cv
    #
    @8
    wcel
    #
    @19
    @5
    wcel
    #
    @4
    @20
    wa
    #
    @21
    @19
    va
    cv
    #
    cA
    cin
    #
    wceq
    #
    va
    @2
    wrex
    #
    @22
    @19
    @2
    wcel
    #
    @19
    @19
    cA
    cin
    #
    wceq
    #
    @26
    @22
    @27
    @19
    cX
    wss
    #
    vv
    cv
    #
    @12
    cima
    #
    @19
    wss
    #
    vv
    cU
    wrex
    #
    vx
    @19
    wral
    #
    @22
    @19
    cA
    cX
    @4
    @20
    @19
    cA
    wss
    #
    vu
    cv
    #
    @12
    cima
    #
    @19
    wss
    #
    vu
    @7
    wrex
    #
    vx
    @19
    wral
    #
    @4
    @7
    cA
    cust
    cfv
    wcel
    #
    @20
    @36
    @41
    wa
    wb
    @1
    @3
    @9
    @42
    @18
    cA
    cU
    cX
    trust
    syldan
    vx
    vu
    @19
    @7
    cA
    elutop
    syl
    #
    simprbda
    #
    @4
    @9
    @20
    @18
    adantr
    sstrd
    @22
    @34
    vx
    @19
    @22
    @11
    @19
    wcel
    #
    wa
    #
    @39
    @34
    vu
    @7
    @46
    @37
    @7
    wcel
    #
    wa
    #
    @39
    wa
    #
    @37
    vw
    cv
    #
    @6
    cin
    #
    wceq
    #
    @34
    vw
    cU
    @49
    @50
    cU
    wcel
    #
    wa
    #
    @52
    wa
    #
    @14
    @34
    vt
    cU
    @55
    @10
    cU
    wcel
    #
    wa
    #
    @14
    wa
    #
    @10
    @50
    cin
    #
    cU
    wcel
    #
    @59
    @12
    cima
    #
    @19
    wss
    #
    @34
    @58
    @1
    @56
    @53
    @60
    @1
    @3
    @20
    @45
    @47
    @39
    @53
    @52
    @56
    @14
    simp-9l
    @55
    @56
    @14
    simplr
    @49
    @53
    @52
    @56
    @14
    simp-4r
    cU
    @10
    @50
    cX
    ustincl
    syl3anc
    @58
    @61
    @13
    @50
    @12
    cima
    #
    cin
    #
    @19
    @10
    @50
    @12
    inimass
    @58
    @64
    @38
    @19
    @58
    @64
    cA
    @63
    cin
    #
    @38
    @14
    @64
    @65
    wss
    @57
    @13
    cA
    @63
    ssrin
    adantl
    @58
    @38
    @51
    @12
    cima
    #
    @65
    @58
    @37
    @51
    @12
    @54
    @52
    @56
    @14
    simpllr
    imaeq1d
    @58
    @11
    cA
    wcel
    #
    @66
    @65
    wceq
    @55
    @67
    @56
    @14
    @55
    @19
    cA
    @11
    @22
    @36
    @45
    @47
    @39
    @53
    @52
    @44
    ad5antr
    @22
    @45
    @47
    @39
    @53
    @52
    simp-5r
    sseldd
    #
    ad2antrr
    @67
    @66
    @63
    cA
    cin
    #
    @65
    @67
    @66
    @63
    @6
    @12
    cima
    #
    cin
    #
    @69
    @11
    cvv
    wcel
    @66
    @71
    wceq
    vx
    vex
    @50
    @6
    @11
    cvv
    inimasn
    ax-mp
    @67
    @70
    cA
    @63
    cA
    cA
    @11
    xpimasn
    ineq2d
    syl5eq
    @63
    cA
    incom
    syl6eq
    syl
    eqtrd
    sseqtr4d
    @48
    @39
    @53
    @52
    @56
    @14
    simp-5r
    sstrd
    syl5ss
    @33
    @62
    vv
    @59
    cU
    @31
    @59
    wceq
    @32
    @61
    @19
    @31
    @59
    @12
    imaeq1
    sseq1d
    rspcev
    syl2anc
    @55
    @4
    @67
    @15
    @49
    @4
    @53
    @52
    @4
    @20
    @45
    @47
    @39
    simp-4l
    #
    ad2antrr
    @68
    @4
    @15
    vx
    cA
    @1
    @3
    @9
    @16
    @17
    simplbda
    r19.21bi
    syl2anc
    r19.29a
    @49
    @4
    @47
    @52
    vw
    cU
    wrex
    #
    @72
    @46
    @47
    @39
    simplr
    @4
    @47
    @73
    @3
    @1
    @6
    cvv
    wcel
    @47
    @73
    wb
    cA
    @2
    sqxpexg
    vw
    @37
    @6
    cU
    @0
    cvv
    elrest
    sylan2
    biimpa
    syl2anc
    r19.29a
    @22
    @40
    vx
    @19
    @4
    @20
    @36
    @41
    @43
    simplbda
    r19.21bi
    r19.29a
    ralrimiva
    @1
    @27
    @30
    @35
    wa
    wb
    @3
    @20
    vx
    vv
    @19
    cU
    cX
    elutop
    ad2antrr
    mpbir2and
    @22
    @28
    @19
    @22
    @36
    @28
    @19
    wceq
    @44
    @19
    cA
    df-ss
    sylib
    eqcomd
    @25
    @29
    va
    @19
    @2
    @23
    @19
    wceq
    @24
    @28
    @19
    @23
    @19
    cA
    ineq1
    eqeq2d
    rspcev
    syl2anc
    @3
    @21
    @26
    wb
    #
    @1
    @20
    @2
    cvv
    wcel
    @3
    @74
    cU
    cutop
    fvex
    va
    @19
    cA
    @2
    cvv
    @2
    elrest
    mpan
    ad2antlr
    mpbird
    ex
    ssrdv
    eqssd
end
