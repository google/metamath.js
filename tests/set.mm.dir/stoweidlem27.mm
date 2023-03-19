include "ccom.mm"
include "cvv.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "wf1o.mm"
include "f1ofn.mm"
include "syl.mm"
include "ovex.mm"
include "sylancl.mm"
include "coexg.mm"
include "wss.mm"
include "f1of.mm"
include "fnfco.mm"
include "rncoss.mm"
include "wceq.mm"
include "wb.mm"
include "fvelrnb.mm"
include "biimpa.mm"
include "crab.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "nfcv.mm"
include "nfv.mm"
include "fveq1.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "elrabf.mm"
include "sylib.mm"
include "simpld.mm"
include "elrnmpt.mm"
include "mpbid.mm"
include "r19.29af.mm"
include "adantlr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "reximdva.mm"
include "mpd.mm"
include "wi.mm"
include "idd.mm"
include "a1i.mm"
include "rexlimdv.mm"
include "ex.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "cuni.mm"
include "sselda.mm"
include "eluni.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt2.mm"
include "dmeqi.mm"
include "rabexgf.mm"
include "adantr.mm"
include "ralrimi.mm"
include "dmmptg.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fvelrn.mm"
include "sylancr.mm"
include "adantrl.mm"
include "simprl.mm"
include "fvco3.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "anbi2d.mm"
include "eleq2.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "eqeltrd.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "reximddv.mm"
include "syldan.mm"
include "simplrl.mm"
include "fvmpt2.mm"
include "adantlrl.mm"
include "simprd.mm"
include "rabid.mm"
include "reximdv.mm"
include "eximd.mm"
include "exlimd.mm"
include "jca32.mm"
include "feq1.mm"
include "fveq1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"

theorem stoweidlem27
  let wph: wff ph
  let vw: setvar w
  let vt: setvar t
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cM: class M
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vl: setvar l
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem27.1: |- G = ( w e. X |-> { h e. Q | w = { t e. T | 0 < ( h ` t ) } } )
  assume stoweidlem27.2: |- ( ph -> Q e. _V )
  assume stoweidlem27.3: |- ( ph -> M e. NN )
  assume stoweidlem27.4: |- ( ph -> Y Fn ran G )
  assume stoweidlem27.5: |- ( ph -> ran G e. _V )
  assume stoweidlem27.6: |- ( ( ph /\ l e. ran G ) -> ( Y ` l ) e. l )
  assume stoweidlem27.7: |- ( ph -> F : ( 1 ... M ) -1-1-onto-> ran G )
  assume stoweidlem27.8: |- ( ph -> ( T \ U ) C_ U. X )
  assume stoweidlem27.9: |- F/ t ph
  assume stoweidlem27.10: |- F/ w ph
  assume stoweidlem27.11: |- F/_ h Q

  disjoint h i
  disjoint h t
  disjoint h w
  disjoint F h
  disjoint i t
  disjoint i w
  disjoint F i
  disjoint t w
  disjoint F t
  disjoint F w
  disjoint h l
  disjoint Y h
  disjoint l t
  disjoint l w
  disjoint Y l
  disjoint Y t
  disjoint Y w
  disjoint T h
  disjoint T w
  disjoint i q
  disjoint q t
  disjoint F q
  disjoint G i
  disjoint M i
  disjoint M q
  disjoint X i
  disjoint X w
  disjoint Y i
  disjoint Y q
  disjoint i ph
  disjoint Q l
  disjoint l ph
  disjoint G l
  disjoint Q q
  disjoint T q
  disjoint U q
  disjoint M w
  disjoint Q w
  disjoint U w
  disjoint k l
  disjoint Q k
  disjoint Y k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. q ( M e. NN /\ ( q : ( 1 ... M ) --> Q /\ A. t e. ( T \ U ) E. i e. ( 1 ... M ) 0 < ( ( q ` i ) ` t ) ) ) )

  proof
    wph
    cY
    cF
    ccom
    #
    cvv
    wcel
    #
    cM
    cn
    wcel
    #
    c1
    cM
    cfz
    co
    #
    cQ
    @0
    wf
    #
    cc0
    vt
    cv
    #
    vi
    cv
    #
    @0
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    vi
    @3
    wrex
    #
    vt
    cT
    cU
    cdif
    #
    wral
    #
    wa
    #
    wa
    #
    @2
    @3
    cQ
    vq
    cv
    #
    wf
    #
    cc0
    @5
    @6
    @15
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    vi
    @3
    wrex
    #
    vt
    @11
    wral
    #
    wa
    #
    wa
    #
    vq
    wex
    wph
    cY
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    @1
    wph
    cY
    cG
    crn
    #
    wfn
    #
    @26
    cvv
    wcel
    @24
    stoweidlem27.4
    stoweidlem27.5
    @26
    cvv
    cY
    fnex
    syl2anc
    wph
    cF
    @3
    wfn
    #
    @3
    cvv
    wcel
    @25
    wph
    @3
    @26
    cF
    wf1o
    #
    @28
    stoweidlem27.7
    @3
    @26
    cF
    f1ofn
    syl
    #
    c1
    cM
    cfz
    ovex
    @3
    cvv
    cF
    fnex
    sylancl
    cY
    cF
    cvv
    cvv
    coexg
    syl2anc
    wph
    @2
    @4
    @12
    stoweidlem27.3
    wph
    @0
    @3
    wfn
    #
    @0
    crn
    #
    cQ
    wss
    @4
    wph
    @27
    @3
    @26
    cF
    wf
    #
    @31
    stoweidlem27.4
    wph
    @29
    @33
    stoweidlem27.7
    @3
    @26
    cF
    f1of
    syl
    #
    @26
    @3
    cY
    cF
    fnfco
    syl2anc
    wph
    @32
    cY
    crn
    #
    cQ
    cY
    cF
    rncoss
    wph
    vk
    @35
    cQ
    wph
    vk
    cv
    #
    @35
    wcel
    #
    @36
    cQ
    wcel
    #
    wph
    @37
    wa
    #
    @38
    vl
    @26
    wrex
    #
    @38
    @39
    vl
    cv
    #
    cY
    cfv
    #
    @36
    wceq
    #
    vl
    @26
    wrex
    #
    @40
    wph
    @37
    @44
    wph
    @27
    @37
    @44
    wb
    stoweidlem27.4
    vl
    @26
    @36
    cY
    fvelrnb
    syl
    biimpa
    @39
    @43
    @38
    vl
    @26
    @39
    @41
    @26
    wcel
    #
    wa
    @42
    cQ
    wcel
    #
    @43
    @38
    wph
    @45
    @46
    @37
    wph
    @45
    wa
    #
    @41
    vw
    cv
    #
    cc0
    @5
    vh
    cv
    #
    cfv
    #
    clt
    wbr
    #
    vt
    cT
    crab
    #
    wceq
    #
    vh
    cQ
    crab
    #
    wceq
    #
    @46
    vw
    cX
    wph
    @45
    vw
    stoweidlem27.10
    vw
    vl
    @26
    vw
    cG
    vw
    cG
    vw
    cX
    @54
    cmpt
    #
    stoweidlem27.1
    vw
    cX
    @54
    nfmpt1
    nfcxfr
    nfrn
    nfcri
    nfan
    @47
    @48
    cX
    wcel
    #
    wa
    #
    @55
    wa
    #
    @46
    @48
    cc0
    @5
    @42
    cfv
    #
    clt
    wbr
    #
    vt
    cT
    crab
    #
    wceq
    #
    @59
    @42
    @54
    wcel
    @46
    @63
    wa
    @59
    @42
    @41
    @54
    @47
    @42
    @41
    wcel
    #
    @57
    @55
    stoweidlem27.6
    ad2antrr
    @58
    @55
    simpr
    eleqtrd
    @53
    @63
    vh
    @42
    cQ
    vh
    @42
    nfcv
    stoweidlem27.11
    @63
    vh
    nfv
    @49
    @42
    wceq
    #
    @52
    @62
    @48
    @65
    @51
    @61
    vt
    cT
    @65
    @50
    @60
    cc0
    clt
    @5
    @49
    @42
    fveq1
    breq2d
    rabbidv
    eqeq2d
    elrabf
    sylib
    simpld
    @47
    @45
    @55
    vw
    cX
    wrex
    #
    wph
    @45
    simpr
    #
    @47
    @45
    @45
    @66
    wb
    @67
    vw
    cX
    @54
    @41
    cG
    @26
    stoweidlem27.1
    elrnmpt
    syl
    mpbid
    r19.29af
    adantlr
    @42
    @36
    cQ
    eleq1
    syl5ibcom
    reximdva
    mpd
    @39
    @38
    @38
    vl
    @26
    @45
    @38
    @38
    wi
    wi
    @39
    @45
    @38
    idd
    a1i
    rexlimdv
    mpd
    ex
    ssrdv
    syl5ss
    @3
    cQ
    @0
    df-f
    sylanbrc
    wph
    @10
    vt
    @11
    stoweidlem27.9
    wph
    @5
    @11
    wcel
    #
    @10
    wph
    @68
    wa
    #
    @10
    vw
    wex
    #
    @10
    @69
    @5
    @48
    wcel
    #
    @57
    wa
    #
    vw
    wex
    #
    @70
    @69
    @5
    cX
    cuni
    #
    wcel
    @73
    wph
    @11
    @74
    @5
    stoweidlem27.8
    sselda
    vw
    @5
    cX
    eluni
    sylib
    @69
    @72
    @10
    vw
    wph
    @68
    vw
    stoweidlem27.10
    @68
    vw
    nfv
    nfan
    #
    wph
    @72
    @10
    wi
    @68
    wph
    @72
    @10
    wph
    @72
    wa
    #
    @7
    @48
    cG
    cfv
    #
    wcel
    #
    vi
    @3
    wrex
    #
    @10
    wph
    @72
    @77
    @26
    wcel
    #
    @79
    wph
    @57
    @80
    @71
    wph
    @57
    wa
    #
    cG
    wfun
    @48
    cG
    cdm
    #
    wcel
    #
    @80
    vw
    cX
    @54
    cG
    stoweidlem27.1
    funmpt2
    wph
    @83
    @57
    wph
    @82
    cX
    @48
    wph
    @82
    @56
    cdm
    #
    cX
    cG
    @56
    stoweidlem27.1
    dmeqi
    wph
    @54
    cvv
    wcel
    #
    vw
    cX
    wral
    @84
    cX
    wceq
    wph
    @85
    vw
    cX
    stoweidlem27.10
    wph
    @57
    @85
    wph
    @85
    @57
    wph
    cQ
    cvv
    wcel
    @85
    stoweidlem27.2
    @53
    vh
    cQ
    cvv
    stoweidlem27.11
    rabexgf
    syl
    adantr
    #
    ex
    ralrimi
    vw
    cX
    @54
    cvv
    dmmptg
    syl
    syl5eq
    eleq2d
    biimpar
    @48
    cG
    fvelrn
    sylancr
    adantrl
    wph
    @80
    wa
    #
    @6
    cF
    cfv
    #
    @77
    wceq
    #
    @78
    vi
    @3
    @87
    @6
    @3
    wcel
    #
    @89
    wa
    #
    wa
    #
    @7
    @77
    cY
    cfv
    #
    @77
    @92
    @7
    @88
    cY
    cfv
    #
    @93
    @92
    @33
    @90
    @7
    @94
    wceq
    wph
    @33
    @80
    @91
    @34
    ad2antrr
    @87
    @90
    @89
    simprl
    @3
    @26
    @6
    cY
    cF
    fvco3
    syl2anc
    @89
    @94
    @93
    wceq
    @87
    @90
    @88
    @77
    cY
    fveq2
    ad2antll
    eqtrd
    @87
    @93
    @77
    wcel
    #
    @91
    wph
    @80
    @95
    @47
    @64
    wi
    @87
    @95
    wi
    vl
    @77
    @26
    @41
    @77
    wceq
    #
    @47
    @87
    @64
    @95
    @96
    @45
    @80
    wph
    @41
    @77
    @26
    eleq1
    anbi2d
    @96
    @64
    @42
    @77
    wcel
    @95
    @41
    @77
    @42
    eleq2
    @96
    @42
    @93
    @77
    @41
    @77
    cY
    fveq2
    eleq1d
    bitrd
    imbi12d
    stoweidlem27.6
    vtoclg
    anabsi7
    adantr
    eqeltrd
    @87
    @77
    cF
    crn
    #
    wcel
    #
    @89
    vi
    @3
    wrex
    #
    wph
    @98
    @80
    wph
    @97
    @26
    @77
    wph
    @29
    @3
    @26
    cF
    wfo
    @97
    @26
    wceq
    stoweidlem27.7
    @3
    @26
    cF
    f1ofo
    @3
    @26
    cF
    forn
    3syl
    eleq2d
    biimpar
    @87
    @28
    @98
    @99
    wb
    wph
    @28
    @80
    @30
    adantr
    vi
    @3
    @77
    cF
    fvelrnb
    syl
    mpbid
    reximddv
    syldan
    @76
    @78
    @9
    vi
    @3
    @76
    @78
    @9
    @76
    @78
    wa
    #
    @5
    cT
    wcel
    #
    @9
    @100
    @5
    @9
    vt
    cT
    crab
    #
    wcel
    @101
    @9
    wa
    @100
    @5
    @48
    @102
    wph
    @71
    @57
    @78
    simplrl
    @100
    @7
    cQ
    wcel
    #
    @48
    @102
    wceq
    #
    @100
    @7
    @54
    wcel
    #
    @103
    @104
    wa
    wph
    @57
    @78
    @105
    @71
    @81
    @78
    @105
    @81
    @77
    @54
    @7
    @81
    @57
    @85
    @77
    @54
    wceq
    wph
    @57
    simpr
    @86
    vw
    cX
    @54
    cvv
    cG
    stoweidlem27.1
    fvmpt2
    syl2anc
    eleq2d
    biimpa
    adantlrl
    @53
    @104
    vh
    @7
    cQ
    vh
    @7
    nfcv
    stoweidlem27.11
    @104
    vh
    nfv
    @49
    @7
    wceq
    #
    @52
    @102
    @48
    @106
    @51
    @9
    vt
    cT
    @106
    @50
    @8
    cc0
    clt
    @5
    @49
    @7
    fveq1
    breq2d
    rabbidv
    eqeq2d
    elrabf
    sylib
    simprd
    eleqtrd
    @9
    vt
    cT
    rabid
    sylib
    simprd
    ex
    reximdv
    mpd
    ex
    adantr
    eximd
    mpd
    @69
    @10
    @10
    vw
    @75
    @10
    vw
    nfv
    @69
    @10
    idd
    exlimd
    mpd
    ex
    ralrimi
    jca32
    @23
    @14
    vq
    @0
    cvv
    @15
    @0
    wceq
    #
    @22
    @13
    @2
    @107
    @16
    @4
    @21
    @12
    @3
    cQ
    @15
    @0
    feq1
    @107
    @20
    @10
    vt
    @11
    @107
    @19
    @9
    vi
    @3
    @107
    @18
    @8
    cc0
    clt
    @107
    @5
    @17
    @7
    @6
    @15
    @0
    fveq1
    fveq1d
    breq2d
    rexbidv
    ralbidv
    anbi12d
    anbi2d
    spcegv
    sylc
end
