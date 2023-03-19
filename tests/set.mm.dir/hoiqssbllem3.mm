include "cv.mm"
include "cfv.mm"
include "cq.mm"
include "c2.mm"
include "chash.mm"
include "csqrt.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cioo.mm"
include "cin.mm"
include "wcel.mm"
include "wral.mm"
include "caddc.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cico.mm"
include "cixp.mm"
include "crrx.mm"
include "cds.mm"
include "cbl.mm"
include "wss.mm"
include "wex.mm"
include "wfn.mm"
include "cvv.mm"
include "qex.mm"
include "inex1.mm"
include "a1i.mm"
include "c0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cr.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "crp.mm"
include "2rp.mm"
include "cn.mm"
include "wne.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnrp.mm"
include "rpsqrtcld.mm"
include "rpmulcld.mm"
include "rpdivcld.mm"
include "adantr.mm"
include "ltsubrpd.mm"
include "rpred.mm"
include "resubcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "rexrd.mm"
include "qinioo.mm"
include "mtbird.mm"
include "neqned.mm"
include "choicefi.mm"
include "simpl.mm"
include "nfra1.mm"
include "rspa.mm"
include "elinel1.mm"
include "ex.mm"
include "ralrimi.mm"
include "adantl.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "simprr.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "ltaddrpd.mm"
include "readdcld.mm"
include "reeanv.mm"
include "nfv.mm"
include "nfan.mm"
include "ad3antrrr.mm"
include "qssre.mm"
include "fssd.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "elin2d.mm"
include "adantlr.mm"
include "adantll.mm"
include "hoiqssbllem1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ineq2d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "sylanbr.mm"
include "hoiqssbllem2.mm"
include "reximdva.mm"

theorem hoiqssbllem3
  let wph: wff ph
  let vi: setvar i
  let cE: class E
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vx: setvar x
  assume hoiqssbllem3.x: |- ( ph -> X e. Fin )
  assume hoiqssbllem3.n: |- ( ph -> X =/= (/) )
  assume hoiqssbllem3.y: |- ( ph -> Y e. ( RR ^m X ) )
  assume hoiqssbllem3.e: |- ( ph -> E e. RR+ )

  disjoint E c
  disjoint E d
  disjoint E i
  disjoint c d
  disjoint c i
  disjoint d i
  disjoint X c
  disjoint X d
  disjoint X i
  disjoint Y c
  disjoint Y d
  disjoint Y i
  disjoint c ph
  disjoint d ph
  disjoint i ph
  disjoint E k
  disjoint c k
  disjoint d k
  disjoint i k
  disjoint X k
  disjoint Y k
  disjoint k x
  assert |- ( ph -> E. c e. ( QQ ^m X ) E. d e. ( QQ ^m X ) ( Y e. X_ i e. X ( ( c ` i ) [,) ( d ` i ) ) /\ X_ i e. X ( ( c ` i ) [,) ( d ` i ) ) C_ ( Y ( ball ` ( dist ` ( RR^ ` X ) ) ) E ) ) )

  proof
    wph
    vi
    cv
    #
    vc
    cv
    #
    cfv
    #
    cq
    @0
    cY
    cfv
    #
    cE
    c2
    cX
    chash
    cfv
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    @3
    cioo
    co
    #
    cin
    #
    wcel
    #
    vi
    cX
    wral
    #
    @0
    vd
    cv
    #
    cfv
    #
    cq
    @3
    @3
    @7
    caddc
    co
    #
    cioo
    co
    #
    cin
    #
    wcel
    #
    vi
    cX
    wral
    #
    wa
    #
    vd
    cq
    cX
    cmap
    co
    #
    wrex
    #
    vc
    @21
    wrex
    #
    cY
    vi
    cX
    @2
    @14
    cico
    co
    cixp
    #
    wcel
    #
    @24
    cY
    cE
    cX
    crrx
    cfv
    cds
    cfv
    cbl
    cfv
    co
    wss
    #
    wa
    #
    vd
    @21
    wrex
    #
    vc
    @21
    wrex
    wph
    @12
    vc
    @21
    wrex
    #
    @19
    vd
    @21
    wrex
    #
    wa
    @23
    wph
    @29
    @30
    wph
    @1
    @21
    wcel
    #
    @12
    wa
    #
    vc
    wex
    #
    @29
    wph
    @1
    cX
    wfn
    #
    @12
    wa
    #
    vc
    wex
    @33
    wph
    vi
    cX
    @10
    vc
    cvv
    hoiqssbllem3.x
    @10
    cvv
    wcel
    wph
    @0
    cX
    wcel
    #
    wa
    #
    cq
    @9
    qex
    inex1
    a1i
    @37
    @10
    c0
    @37
    @10
    c0
    wceq
    @3
    @8
    cle
    wbr
    #
    @37
    @8
    @3
    clt
    wbr
    @38
    wn
    @37
    @3
    @7
    wph
    cX
    cr
    @0
    cY
    wph
    cY
    cr
    cX
    cmap
    co
    wcel
    #
    cX
    cr
    cY
    wf
    hoiqssbllem3.y
    cY
    cr
    cX
    elmapi
    syl
    ffvelrnda
    #
    wph
    @7
    crp
    wcel
    @36
    wph
    cE
    @6
    hoiqssbllem3.e
    wph
    c2
    @5
    c2
    crp
    wcel
    wph
    2rp
    a1i
    wph
    @4
    wph
    @4
    cn
    wcel
    #
    @4
    crp
    wcel
    wph
    @41
    cX
    c0
    wne
    #
    hoiqssbllem3.n
    wph
    cX
    cfn
    wcel
    #
    @41
    @42
    wb
    hoiqssbllem3.x
    cX
    hashnncl
    syl
    mpbird
    @4
    nnrp
    syl
    rpsqrtcld
    rpmulcld
    rpdivcld
    adantr
    #
    ltsubrpd
    @37
    @8
    @3
    @37
    @3
    @7
    @40
    @37
    @7
    @44
    rpred
    #
    resubcld
    #
    @40
    ltnled
    mpbid
    @37
    @8
    @3
    @37
    @8
    @46
    rexrd
    @37
    @3
    @40
    rexrd
    #
    qinioo
    mtbird
    neqned
    choicefi
    wph
    @35
    @32
    vc
    wph
    @35
    @32
    wph
    @35
    wa
    #
    @31
    @12
    @48
    @31
    cX
    cq
    @1
    wf
    #
    @48
    @34
    @2
    cq
    wcel
    #
    vi
    cX
    wral
    #
    wa
    #
    @49
    @35
    @52
    wph
    @35
    @34
    @51
    @34
    @12
    simpl
    @12
    @51
    @34
    @12
    @50
    vi
    cX
    @11
    vi
    cX
    nfra1
    #
    @12
    @36
    @50
    @12
    @36
    wa
    #
    @11
    @50
    @11
    vi
    cX
    rspa
    #
    @2
    cq
    @9
    elinel1
    syl
    ex
    ralrimi
    adantl
    jca
    adantl
    vi
    cX
    cq
    @1
    ffnfv
    sylibr
    wph
    @31
    @49
    wb
    #
    @35
    wph
    cq
    cvv
    wcel
    #
    @43
    @56
    @57
    wph
    qex
    a1i
    #
    hoiqssbllem3.x
    cq
    cX
    @1
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    wph
    @34
    @12
    simprr
    jca
    ex
    eximdv
    mpd
    @12
    vc
    @21
    df-rex
    sylibr
    wph
    @13
    @21
    wcel
    #
    @19
    wa
    #
    vd
    wex
    #
    @30
    wph
    @13
    cX
    wfn
    #
    @19
    wa
    #
    vd
    wex
    @61
    wph
    vi
    cX
    @17
    vd
    cvv
    hoiqssbllem3.x
    @17
    cvv
    wcel
    @37
    cq
    @16
    qex
    inex1
    a1i
    @37
    @17
    c0
    @37
    @17
    c0
    wceq
    @15
    @3
    cle
    wbr
    #
    @37
    @3
    @15
    clt
    wbr
    @64
    wn
    @37
    @3
    @7
    @40
    @44
    ltaddrpd
    @37
    @3
    @15
    @40
    @37
    @3
    @7
    @40
    @45
    readdcld
    #
    ltnled
    mpbid
    @37
    @3
    @15
    @47
    @37
    @15
    @65
    rexrd
    qinioo
    mtbird
    neqned
    choicefi
    wph
    @63
    @60
    vd
    wph
    @63
    @60
    wph
    @63
    wa
    #
    @59
    @19
    @66
    @59
    cX
    cq
    @13
    wf
    #
    @66
    @62
    @14
    cq
    wcel
    #
    vi
    cX
    wral
    #
    wa
    #
    @67
    @63
    @70
    wph
    @63
    @62
    @69
    @62
    @19
    simpl
    @19
    @69
    @62
    @19
    @68
    vi
    cX
    @18
    vi
    cX
    nfra1
    #
    @19
    @36
    @68
    @19
    @36
    wa
    #
    @18
    @68
    @18
    vi
    cX
    rspa
    #
    @14
    cq
    @16
    elinel1
    syl
    ex
    ralrimi
    adantl
    jca
    adantl
    vi
    cX
    cq
    @13
    ffnfv
    sylibr
    wph
    @59
    @67
    wb
    #
    @63
    wph
    @57
    @43
    @74
    @58
    hoiqssbllem3.x
    cq
    cX
    @13
    cvv
    cfn
    elmapg
    syl2anc
    adantr
    mpbird
    wph
    @62
    @19
    simprr
    jca
    ex
    eximdv
    mpd
    @19
    vd
    @21
    df-rex
    sylibr
    jca
    @12
    @19
    vc
    vd
    @21
    @21
    reeanv
    sylibr
    wph
    @22
    @28
    vc
    @21
    wph
    @31
    wa
    #
    @20
    @27
    vd
    @21
    @75
    @59
    wa
    #
    @20
    @27
    @76
    @20
    wa
    #
    @25
    @26
    @77
    @1
    @13
    vi
    cE
    cX
    cY
    @76
    @20
    vi
    @76
    vi
    nfv
    @12
    @19
    vi
    @53
    @71
    nfan
    nfan
    wph
    @43
    @31
    @59
    @20
    hoiqssbllem3.x
    ad3antrrr
    wph
    @42
    @31
    @59
    @20
    hoiqssbllem3.n
    ad3antrrr
    wph
    @39
    @31
    @59
    @20
    hoiqssbllem3.y
    ad3antrrr
    @75
    cX
    cr
    @1
    wf
    #
    @59
    @20
    @31
    @78
    wph
    @31
    cX
    cq
    cr
    @1
    @1
    cq
    cX
    elmapi
    cq
    cr
    wss
    #
    @31
    qssre
    a1i
    fssd
    adantl
    #
    ad2antrr
    @59
    cX
    cr
    @13
    wf
    #
    @75
    @20
    @59
    cX
    cq
    cr
    @13
    @13
    cq
    cX
    elmapi
    @79
    @59
    qssre
    a1i
    fssd
    #
    ad2antlr
    wph
    cE
    crp
    wcel
    #
    @31
    @59
    @20
    hoiqssbllem3.e
    ad3antrrr
    @20
    @36
    @2
    @9
    wcel
    #
    @76
    @12
    @36
    @84
    @19
    @54
    cq
    @9
    @2
    @55
    elin2d
    #
    adantlr
    adantll
    @20
    @36
    @14
    @16
    wcel
    #
    @76
    @19
    @36
    @86
    @12
    @72
    cq
    @16
    @14
    @73
    elin2d
    #
    adantll
    adantll
    hoiqssbllem1
    @77
    @76
    vk
    cv
    #
    @1
    cfv
    #
    cq
    @88
    cY
    cfv
    #
    @7
    cmin
    co
    #
    @90
    cioo
    co
    #
    cin
    #
    wcel
    #
    vk
    cX
    wral
    #
    @88
    @13
    cfv
    #
    cq
    @90
    @90
    @7
    caddc
    co
    #
    cioo
    co
    #
    cin
    #
    wcel
    #
    vk
    cX
    wral
    #
    wa
    #
    @26
    @76
    @20
    simpl
    @20
    @102
    @76
    @20
    @95
    @101
    @12
    @95
    @19
    @12
    @95
    @11
    @94
    vi
    vk
    cX
    @0
    @88
    wceq
    #
    @2
    @89
    @10
    @93
    @0
    @88
    @1
    fveq2
    @103
    @9
    @92
    cq
    @103
    @8
    @91
    @3
    @90
    cioo
    @103
    @3
    @90
    @7
    cmin
    @0
    @88
    cY
    fveq2
    #
    oveq1d
    @104
    oveq12d
    ineq2d
    eleq12d
    cbvralv
    #
    biimpi
    adantr
    @19
    @101
    @12
    @19
    @101
    @18
    @100
    vi
    vk
    cX
    @103
    @14
    @96
    @17
    @99
    @0
    @88
    @13
    fveq2
    @103
    @16
    @98
    cq
    @103
    @3
    @90
    @15
    @97
    cioo
    @104
    @103
    @3
    @90
    @7
    caddc
    @104
    oveq1d
    oveq12d
    ineq2d
    eleq12d
    cbvralv
    #
    biimpi
    adantl
    jca
    adantl
    @76
    @102
    wa
    #
    @1
    @13
    vi
    cE
    cX
    cY
    @107
    vi
    nfv
    wph
    @43
    @31
    @59
    @102
    hoiqssbllem3.x
    ad3antrrr
    wph
    @42
    @31
    @59
    @102
    hoiqssbllem3.n
    ad3antrrr
    wph
    @39
    @31
    @59
    @102
    hoiqssbllem3.y
    ad3antrrr
    @75
    @78
    @59
    @102
    @80
    ad2antrr
    @59
    @81
    @75
    @102
    @82
    ad2antlr
    wph
    @83
    @31
    @59
    @102
    hoiqssbllem3.e
    ad3antrrr
    @102
    @36
    @84
    @76
    @95
    @36
    @84
    @101
    @95
    @12
    @36
    @84
    @105
    @85
    sylanbr
    adantlr
    adantll
    @102
    @36
    @86
    @76
    @101
    @36
    @86
    @95
    @101
    @19
    @36
    @86
    @106
    @87
    sylanbr
    adantll
    adantll
    hoiqssbllem2
    syl2anc
    jca
    ex
    reximdva
    reximdva
    mpd
end
