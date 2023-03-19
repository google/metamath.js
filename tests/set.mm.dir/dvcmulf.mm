include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "caddc.mm"
include "cc.mm"
include "wcel.mm"
include "wf.mm"
include "fconstg.mm"
include "syl.mm"
include "snssd.mm"
include "fssd.mm"
include "cc0.mm"
include "cdm.mm"
include "wceq.mm"
include "c0ex.mm"
include "fconst.mm"
include "cres.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "cnt.mm"
include "wss.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "ssid.mm"
include "a1i.mm"
include "dvbsss.mm"
include "eqsstr3d.mm"
include "eqid.mm"
include "dvres.mm"
include "syl22anc.mm"
include "cmpt.mm"
include "resmptd.mm"
include "fconstmpt.mm"
include "reseq1i.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "dvconst.mm"
include "dmeqd.mm"
include "fdmi.mm"
include "syl6eq.mm"
include "sseqtr4d.mm"
include "dvres3.mm"
include "xpssres.mm"
include "reseq1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "topontop.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "dvbssntr.mm"
include "eqssd.mm"
include "reseq12d.mm"
include "3eqtr4d.mm"
include "feq1d.mm"
include "mpbiri.mm"
include "fdm.mm"
include "dvmulf.mm"
include "cin.mm"
include "cv.mm"
include "sseqin2.mm"
include "sylib.mm"
include "mpteq1d.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "ssexd.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "inidm.mm"
include "dvfg.mm"
include "feq2d.mm"
include "mpbid.mm"
include "0cnd.mm"
include "ovexd.mm"
include "oveq1d.mm"
include "mul02.mm"
include "adantl.mm"
include "caofid2.mm"
include "fvexd.mm"
include "adantr.mm"
include "feqmptd.mm"
include "offval2.mm"
include "ffvelrnda.mm"
include "mulcld.mm"
include "addid2d.mm"
include "mulcomd.mm"
include "mpteq2dva.mm"

theorem dvcmulf
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cX: class X
  let vx: setvar x
  assume dvcmul.s: |- ( ph -> S e. { RR , CC } )
  assume dvcmul.f: |- ( ph -> F : X --> CC )
  assume dvcmul.a: |- ( ph -> A e. CC )
  assume dvcmulf.df: |- ( ph -> dom ( S _D F ) = X )


  assert |- ( ph -> ( S _D ( ( S X. { A } ) oF x. F ) ) = ( ( S X. { A } ) oF x. ( S _D F ) ) )

  proof
    wph
    cS
    cX
    cA
    csn
    #
    cxp
    #
    cF
    cmul
    cof
    #
    co
    #
    cdv
    co
    cS
    @1
    cdv
    co
    #
    cF
    @2
    co
    #
    cS
    cF
    cdv
    co
    #
    @1
    @2
    co
    #
    caddc
    cof
    co
    #
    cS
    cS
    @0
    cxp
    #
    cF
    @2
    co
    #
    cdv
    co
    @9
    @6
    @2
    co
    #
    wph
    cS
    @1
    cF
    cX
    dvcmul.s
    wph
    cX
    @0
    cc
    @1
    wph
    cA
    cc
    wcel
    #
    cX
    @0
    @1
    wf
    #
    dvcmul.a
    cX
    cA
    cc
    fconstg
    syl
    #
    wph
    cA
    cc
    dvcmul.a
    snssd
    #
    fssd
    dvcmul.f
    wph
    cX
    cc0
    csn
    #
    @4
    wf
    #
    @4
    cdm
    cX
    wceq
    wph
    @17
    cX
    @16
    cX
    @16
    cxp
    #
    wf
    cX
    cc0
    c0ex
    fconst
    wph
    cX
    @16
    @4
    @18
    wph
    cS
    @9
    cX
    cres
    #
    cdv
    co
    #
    cS
    @9
    cdv
    co
    #
    cX
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @4
    @18
    wph
    cS
    cc
    wss
    #
    cS
    cc
    @9
    wf
    cS
    cS
    wss
    #
    cX
    cS
    wss
    #
    @20
    @25
    wceq
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @26
    dvcmul.s
    cS
    recnprss
    syl
    #
    wph
    cS
    @0
    cc
    @9
    wph
    @12
    cS
    @0
    @9
    wf
    #
    dvcmul.a
    cS
    cA
    cc
    fconstg
    syl
    #
    @15
    fssd
    @27
    wph
    cS
    ssid
    a1i
    wph
    cX
    @6
    cdm
    #
    cS
    dvcmulf.df
    @34
    cS
    wss
    wph
    cS
    cF
    dvbsss
    a1i
    eqsstr3d
    #
    cS
    cX
    cS
    @23
    @9
    @22
    @22
    eqid
    #
    @23
    eqid
    #
    dvres
    syl22anc
    wph
    @19
    @1
    cS
    cdv
    wph
    vx
    cS
    cA
    cmpt
    #
    cX
    cres
    vx
    cX
    cA
    cmpt
    #
    @19
    @1
    wph
    vx
    cS
    cX
    cA
    @35
    resmptd
    @9
    @38
    cX
    vx
    cS
    cA
    fconstmpt
    reseq1i
    vx
    cX
    cA
    fconstmpt
    #
    3eqtr4g
    oveq2d
    wph
    vx
    cS
    cc0
    cmpt
    #
    cX
    cres
    vx
    cX
    cc0
    cmpt
    #
    @25
    @18
    wph
    vx
    cS
    cX
    cc0
    @35
    resmptd
    wph
    @21
    @41
    @24
    cX
    wph
    @21
    cS
    @16
    cxp
    #
    @41
    wph
    cS
    cc
    @0
    cxp
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @44
    cdv
    co
    #
    cS
    cres
    #
    @21
    @43
    wph
    @30
    cc
    cc
    @44
    wf
    cc
    cc
    wss
    #
    cS
    @47
    cdm
    #
    wss
    @46
    @48
    wceq
    dvcmul.s
    wph
    cc
    @0
    cc
    @44
    wph
    @12
    cc
    @0
    @44
    wf
    dvcmul.a
    cc
    cA
    cc
    fconstg
    syl
    @15
    fssd
    @49
    wph
    cc
    ssid
    a1i
    wph
    cS
    cc
    @50
    @31
    wph
    @50
    cc
    @16
    cxp
    #
    cdm
    cc
    wph
    @47
    @51
    wph
    @12
    @47
    @51
    wceq
    dvcmul.a
    cA
    dvconst
    syl
    #
    dmeqd
    cc
    @16
    @51
    cc
    cc0
    c0ex
    fconst
    fdmi
    syl6eq
    sseqtr4d
    cc
    cS
    @44
    dvres3
    syl22anc
    wph
    @45
    @9
    cS
    cdv
    wph
    @26
    @45
    @9
    wceq
    @31
    cc
    @0
    cS
    xpssres
    syl
    oveq2d
    wph
    @48
    @51
    cS
    cres
    #
    @43
    wph
    @47
    @51
    cS
    @52
    reseq1d
    wph
    @26
    @53
    @43
    wceq
    @31
    cc
    @16
    cS
    xpssres
    syl
    eqtrd
    3eqtr3d
    vx
    cS
    cc0
    fconstmpt
    syl6eq
    wph
    @24
    cX
    wph
    @23
    ctop
    wcel
    #
    cX
    @23
    cuni
    #
    wss
    @24
    cX
    wss
    wph
    @23
    cS
    ctopon
    cfv
    wcel
    #
    @54
    wph
    @22
    cc
    ctopon
    cfv
    wcel
    @26
    @56
    @22
    @36
    cnfldtopon
    @31
    cS
    @22
    cc
    resttopon
    sylancr
    #
    cS
    @23
    topontop
    syl
    wph
    cX
    cS
    @55
    @35
    wph
    @56
    cS
    @55
    wceq
    @57
    cS
    @23
    toponuni
    syl
    sseqtrd
    cX
    @23
    @55
    @55
    eqid
    ntrss2
    syl2anc
    wph
    cX
    @34
    @24
    dvcmulf.df
    wph
    cX
    cS
    cF
    @23
    @22
    @31
    dvcmul.f
    @35
    @37
    @36
    dvbssntr
    eqsstr3d
    eqssd
    reseq12d
    @18
    @42
    wceq
    wph
    vx
    cX
    cc0
    fconstmpt
    #
    a1i
    3eqtr4d
    3eqtr3d
    #
    feq1d
    mpbiri
    cX
    @16
    @4
    fdm
    syl
    dvcmulf.df
    dvmulf
    wph
    @10
    @3
    cS
    cdv
    wph
    vx
    cS
    cX
    cin
    #
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    vx
    cX
    @63
    cmpt
    @10
    @3
    wph
    vx
    @60
    cX
    @63
    wph
    @28
    @60
    cX
    wceq
    @35
    cX
    cS
    sseqin2
    sylib
    #
    mpteq1d
    wph
    vx
    cS
    cX
    cA
    @62
    cmul
    @60
    @9
    cF
    @29
    cvv
    wph
    @32
    @9
    cS
    wfn
    @33
    cS
    @0
    @9
    ffn
    syl
    #
    wph
    cX
    cc
    cF
    wf
    cF
    cX
    wfn
    dvcmul.f
    cX
    cc
    cF
    ffn
    syl
    #
    dvcmul.s
    wph
    cX
    cS
    @29
    dvcmul.s
    @35
    ssexd
    #
    @60
    eqid
    #
    wph
    @12
    @61
    cS
    wcel
    @61
    @9
    cfv
    cA
    wceq
    dvcmul.a
    cS
    cA
    @61
    cc
    fvconst2g
    sylan
    #
    wph
    @61
    cX
    wcel
    #
    wa
    #
    @62
    eqidd
    #
    offval
    wph
    vx
    cX
    cX
    cA
    @62
    cmul
    cX
    @1
    cF
    cvv
    cvv
    wph
    @13
    @1
    cX
    wfn
    @14
    cX
    @0
    @1
    ffn
    syl
    @66
    @67
    @67
    cX
    inidm
    wph
    @12
    @70
    @61
    @1
    cfv
    cA
    wceq
    dvcmul.a
    cX
    cA
    @61
    cc
    fvconst2g
    sylan
    @72
    offval
    3eqtr4d
    oveq2d
    wph
    vx
    @60
    cA
    @61
    @6
    cfv
    #
    cmul
    co
    #
    cmpt
    vx
    cX
    @74
    cmpt
    #
    @11
    @8
    wph
    vx
    @60
    cX
    @74
    @64
    mpteq1d
    wph
    vx
    cS
    cX
    cA
    @73
    cmul
    @60
    @9
    @6
    @29
    cvv
    @65
    wph
    cX
    cc
    @6
    wf
    #
    @6
    cX
    wfn
    wph
    @34
    cc
    @6
    wf
    #
    @76
    wph
    @30
    @77
    dvcmul.s
    cS
    cF
    dvfg
    syl
    wph
    @34
    cX
    cc
    @6
    dvcmulf.df
    feq2d
    mpbid
    #
    cX
    cc
    @6
    ffn
    syl
    dvcmul.s
    @67
    @68
    @69
    @71
    @73
    eqidd
    offval
    wph
    @8
    vx
    cX
    cc0
    @73
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @75
    wph
    vx
    cX
    cc0
    @79
    caddc
    @5
    @7
    cvv
    cc
    cvv
    @67
    @71
    0cnd
    @71
    @73
    cA
    cmul
    ovexd
    wph
    @5
    @18
    @42
    wph
    @5
    @18
    cF
    @2
    co
    @18
    wph
    @4
    @18
    cF
    @2
    @59
    oveq1d
    wph
    vx
    cX
    cc0
    cc0
    cmul
    cc
    cF
    cvv
    cc
    cc
    @67
    dvcmul.f
    wph
    0cnd
    #
    @81
    @61
    cc
    wcel
    cc0
    @61
    cmul
    co
    cc0
    wceq
    wph
    @61
    mul02
    adantl
    caofid2
    eqtrd
    @58
    syl6eq
    wph
    vx
    cX
    @73
    cA
    cmul
    @6
    @1
    cvv
    cvv
    cc
    @67
    @71
    @61
    @6
    fvexd
    wph
    @12
    @70
    dvcmul.a
    adantr
    #
    wph
    vx
    cX
    cc
    @6
    @78
    feqmptd
    @1
    @39
    wceq
    wph
    @40
    a1i
    offval2
    offval2
    wph
    vx
    cX
    @80
    @74
    @71
    @80
    @79
    @74
    @71
    @79
    @71
    @73
    cA
    wph
    cX
    cc
    @61
    @6
    @78
    ffvelrnda
    #
    @82
    mulcld
    addid2d
    @71
    @73
    cA
    @83
    @82
    mulcomd
    eqtrd
    mpteq2dva
    eqtrd
    3eqtr4d
    3eqtr4d
end
