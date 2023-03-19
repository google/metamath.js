include "cqtop.mm"
include "co.mm"
include "crest.mm"
include "cres.mm"
include "ccn.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "crn.mm"
include "wceq.mm"
include "wss.mm"
include "cuni.mm"
include "wfn.mm"
include "wfo.mm"
include "fofn.mm"
include "syl.mm"
include "qtopid.mm"
include "syl2anc.mm"
include "ccnv.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cnrest.mm"
include "wb.mm"
include "qtoptopon.mm"
include "df-ima.mm"
include "imaeq2d.mm"
include "foimacnv.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqimss.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "resttopon.mm"
include "qtopss.mm"
include "cv.mm"
include "wa.mm"
include "wfun.mm"
include "fnfun.mm"
include "sseqtr4d.mm"
include "fores.mm"
include "foeq3.mm"
include "elqtop3.mm"
include "cin.mm"
include "cnvresima.mm"
include "imass2.mm"
include "adantl.mm"
include "adantr.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "ccld.mm"
include "simplrl.mm"
include "ctop.mm"
include "cvv.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "toponmax.mm"
include "fornex.mm"
include "sylc.mm"
include "ssexd.mm"
include "sstrd.mm"
include "restopn2.mm"
include "sylan.mm"
include "simprbda.mm"
include "adantrl.mm"
include "an32s.mm"
include "mpbir2and.mm"
include "elrestr.mm"
include "eqeltrrd.mm"
include "cdif.mm"
include "difeq1d.mm"
include "ssdifssd.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "3syl.mm"
include "eqtr4d.mm"
include "simpr.mm"
include "simplrr.mm"
include "opncld.mm"
include "eqeltrd.mm"
include "restcldr.mm"
include "qtopcld.mm"
include "difssd.mm"
include "restcldi.mm"
include "isopn2.mm"
include "mpbird.mm"
include "wo.mm"
include "mpjaodan.mm"
include "expr.mm"
include "sylbid.mm"
include "expimpd.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem qtoprest
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume qtoprest.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume qtoprest.3: |- ( ph -> F : X -onto-> Y )
  assume qtoprest.4: |- ( ph -> U C_ Y )
  assume qtoprest.5: |- ( ph -> A = ( `' F " U ) )
  assume qtoprest.6: |- ( ph -> ( A e. J \/ A e. ( Clsd ` J ) ) )


  assert |- ( ph -> ( ( J qTop F ) |`t U ) = ( ( J |`t A ) qTop ( F |` A ) ) )

  proof
    wph
    cJ
    cF
    cqtop
    co
    #
    cU
    crest
    co
    #
    cJ
    cA
    crest
    co
    #
    cF
    cA
    cres
    #
    cqtop
    co
    #
    wph
    @3
    @2
    @1
    ccn
    co
    wcel
    #
    @1
    cU
    ctopon
    cfv
    wcel
    #
    @3
    crn
    #
    cU
    wceq
    #
    @1
    @4
    wss
    wph
    @3
    @2
    @0
    ccn
    co
    wcel
    #
    @5
    wph
    cF
    cJ
    @0
    ccn
    co
    wcel
    #
    cA
    cJ
    cuni
    #
    wss
    @9
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    wfn
    #
    @10
    qtoprest.2
    wph
    cX
    cY
    cF
    wfo
    #
    @13
    qtoprest.3
    cX
    cY
    cF
    fofn
    syl
    #
    cF
    cJ
    cX
    qtopid
    syl2anc
    wph
    cA
    cX
    @11
    wph
    cA
    cF
    ccnv
    #
    cU
    cima
    #
    cX
    qtoprest.5
    wph
    cF
    cdm
    #
    @17
    cX
    cF
    cU
    cnvimass
    wph
    @13
    @18
    cX
    wceq
    @15
    cX
    cF
    fndm
    syl
    #
    syl5sseq
    eqsstrd
    #
    wph
    @12
    cX
    @11
    wceq
    qtoprest.2
    cX
    cJ
    toponuni
    syl
    sseqtrd
    cA
    cF
    cJ
    @0
    @11
    @11
    eqid
    cnrest
    syl2anc
    wph
    @0
    cY
    ctopon
    cfv
    wcel
    #
    @7
    cU
    wss
    #
    cU
    cY
    wss
    #
    @9
    @5
    wb
    wph
    @12
    @14
    @21
    qtoprest.2
    qtoprest.3
    cF
    cJ
    cX
    cY
    qtoptopon
    syl2anc
    #
    wph
    @8
    @22
    wph
    @7
    cF
    cA
    cima
    #
    cU
    cF
    cA
    df-ima
    wph
    @25
    cF
    @17
    cima
    #
    cU
    wph
    cA
    @17
    cF
    qtoprest.5
    imaeq2d
    wph
    @14
    @23
    @26
    cU
    wceq
    qtoprest.3
    qtoprest.4
    cX
    cY
    cU
    cF
    foimacnv
    syl2anc
    eqtrd
    #
    syl5eqr
    #
    @7
    cU
    eqimss
    syl
    qtoprest.4
    cU
    @3
    @2
    @0
    cY
    cnrest2
    syl3anc
    mpbid
    wph
    @21
    @23
    @6
    @24
    qtoprest.4
    cU
    @0
    cY
    resttopon
    syl2anc
    #
    @28
    @3
    @2
    @1
    cU
    qtopss
    syl3anc
    wph
    vx
    @4
    @1
    wph
    vx
    cv
    #
    @4
    wcel
    #
    @30
    cU
    wss
    #
    @3
    ccnv
    @30
    cima
    #
    @2
    wcel
    #
    wa
    #
    @30
    @1
    wcel
    #
    wph
    @2
    cA
    ctopon
    cfv
    wcel
    #
    cA
    cU
    @3
    wfo
    #
    @31
    @35
    wb
    wph
    @12
    cA
    cX
    wss
    @37
    qtoprest.2
    @20
    cA
    cJ
    cX
    resttopon
    syl2anc
    #
    wph
    cA
    @25
    @3
    wfo
    #
    @38
    wph
    cF
    wfun
    #
    cA
    @18
    wss
    @40
    wph
    @13
    @41
    @15
    cX
    cF
    fnfun
    syl
    #
    wph
    cA
    cX
    @18
    @20
    @19
    sseqtr4d
    cA
    cF
    fores
    syl2anc
    wph
    @25
    cU
    wceq
    @40
    @38
    wb
    @27
    @25
    cU
    cA
    @3
    foeq3
    syl
    mpbid
    @30
    @3
    @2
    cA
    cU
    elqtop3
    syl2anc
    wph
    @32
    @34
    @36
    wph
    @32
    wa
    #
    @34
    @16
    @30
    cima
    #
    @2
    wcel
    #
    @36
    @43
    @33
    @44
    @2
    @43
    @33
    @44
    cA
    cin
    #
    @44
    cA
    @30
    cF
    cnvresima
    @43
    @44
    cA
    wss
    #
    @46
    @44
    wceq
    @43
    @44
    @17
    cA
    @32
    @44
    @17
    wss
    wph
    @30
    cU
    @16
    imass2
    adantl
    wph
    cA
    @17
    wceq
    #
    @32
    qtoprest.5
    adantr
    sseqtr4d
    @44
    cA
    df-ss
    sylib
    syl5eq
    eleq1d
    wph
    @32
    @45
    @36
    wph
    @32
    @45
    wa
    #
    wa
    #
    cA
    cJ
    wcel
    #
    @36
    cA
    cJ
    ccld
    cfv
    #
    wcel
    #
    @50
    @51
    wa
    #
    @30
    cU
    cin
    #
    @30
    @1
    @54
    @32
    @55
    @30
    wceq
    wph
    @32
    @45
    @51
    simplrl
    #
    @30
    cU
    df-ss
    sylib
    @54
    @0
    ctop
    wcel
    #
    cU
    cvv
    wcel
    #
    @30
    @0
    wcel
    #
    @55
    @1
    wcel
    wph
    @57
    @49
    @51
    wph
    @21
    @57
    @24
    cY
    @0
    topontop
    syl
    ad2antrr
    wph
    @58
    @49
    @51
    wph
    cU
    cY
    cvv
    wph
    cX
    cJ
    wcel
    #
    @14
    cY
    cvv
    wcel
    wph
    @12
    @60
    qtoprest.2
    cX
    cJ
    toponmax
    syl
    qtoprest.3
    cX
    cY
    cJ
    cF
    fornex
    sylc
    qtoprest.4
    ssexd
    ad2antrr
    @54
    @59
    @30
    cY
    wss
    #
    @44
    cJ
    wcel
    #
    @54
    @30
    cU
    cY
    @56
    wph
    @23
    @49
    @51
    qtoprest.4
    ad2antrr
    sstrd
    wph
    @51
    @49
    @62
    wph
    @51
    wa
    #
    @45
    @62
    @32
    @63
    @45
    @62
    @47
    wph
    cJ
    ctop
    wcel
    #
    @51
    @45
    @62
    @47
    wa
    wb
    wph
    @12
    @64
    qtoprest.2
    cX
    cJ
    topontop
    syl
    cA
    @44
    cJ
    restopn2
    sylan
    simprbda
    adantrl
    an32s
    wph
    @59
    @61
    @62
    wa
    wb
    #
    @49
    @51
    wph
    @12
    @14
    @65
    qtoprest.2
    qtoprest.3
    @30
    cF
    cJ
    cX
    cY
    elqtop3
    syl2anc
    ad2antrr
    mpbir2and
    @30
    cU
    @0
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    @50
    @53
    wa
    #
    @36
    @1
    cuni
    #
    @30
    cdif
    #
    @1
    ccld
    cfv
    #
    wcel
    #
    @66
    cU
    @30
    cdif
    #
    @68
    @69
    @66
    cU
    @67
    @30
    @66
    @6
    cU
    @67
    wceq
    wph
    @6
    @49
    @53
    @29
    ad2antrr
    #
    cU
    @1
    toponuni
    syl
    #
    difeq1d
    @66
    cU
    @0
    cuni
    #
    wss
    @71
    @0
    ccld
    cfv
    wcel
    #
    @71
    cU
    wss
    @71
    @69
    wcel
    @66
    cU
    cY
    @74
    wph
    @23
    @49
    @53
    qtoprest.4
    ad2antrr
    #
    @66
    @21
    cY
    @74
    wceq
    wph
    @21
    @49
    @53
    @24
    ad2antrr
    cY
    @0
    toponuni
    syl
    sseqtrd
    @66
    @75
    @71
    cY
    wss
    #
    @16
    @71
    cima
    #
    @52
    wcel
    #
    @66
    cU
    cY
    @30
    @76
    ssdifssd
    @66
    @78
    cA
    @44
    cdif
    #
    @52
    @66
    @78
    @17
    @44
    cdif
    #
    @80
    @66
    @41
    @16
    ccnv
    wfun
    @78
    @81
    wceq
    wph
    @41
    @49
    @53
    @42
    ad2antrr
    cF
    funcnvcnv
    cU
    @30
    @16
    imadif
    3syl
    @66
    cA
    @17
    @44
    wph
    @48
    @49
    @53
    qtoprest.5
    ad2antrr
    difeq1d
    eqtr4d
    @66
    @53
    @80
    @2
    ccld
    cfv
    #
    wcel
    @80
    @52
    wcel
    @50
    @53
    simpr
    @66
    @80
    @2
    cuni
    #
    @44
    cdif
    #
    @82
    @66
    cA
    @83
    @44
    @66
    @37
    cA
    @83
    wceq
    wph
    @37
    @49
    @53
    @39
    ad2antrr
    #
    cA
    @2
    toponuni
    syl
    difeq1d
    @66
    @2
    ctop
    wcel
    #
    @45
    @84
    @82
    wcel
    @66
    @37
    @86
    @85
    cA
    @2
    topontop
    syl
    wph
    @32
    @45
    @53
    simplrr
    @44
    @2
    @83
    @83
    eqid
    opncld
    syl2anc
    eqeltrd
    cA
    @80
    cJ
    restcldr
    syl2anc
    eqeltrd
    wph
    @75
    @77
    @79
    wa
    wb
    #
    @49
    @53
    wph
    @12
    @14
    @87
    qtoprest.2
    qtoprest.3
    @71
    cF
    cJ
    cX
    cY
    qtopcld
    syl2anc
    ad2antrr
    mpbir2and
    @66
    cU
    @30
    difssd
    cU
    @71
    @0
    @74
    @74
    eqid
    restcldi
    syl3anc
    eqeltrrd
    @66
    @1
    ctop
    wcel
    #
    @30
    @67
    wss
    @36
    @70
    wb
    @66
    @6
    @88
    @72
    cU
    @1
    topontop
    syl
    @66
    @30
    cU
    @67
    wph
    @32
    @45
    @53
    simplrl
    @73
    sseqtrd
    @30
    @1
    @67
    @67
    eqid
    isopn2
    syl2anc
    mpbird
    wph
    @51
    @53
    wo
    @49
    qtoprest.6
    adantr
    mpjaodan
    expr
    sylbid
    expimpd
    sylbid
    ssrdv
    eqssd
end
