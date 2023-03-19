include "cn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxad.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cfv.mm"
include "cesum.mm"
include "wss.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wceq.mm"
include "wfn.mm"
include "cuz.mm"
include "cz.mm"
include "1z.mm"
include "seqfn.mm"
include "ax-mp.mm"
include "nnuz.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "wa.mm"
include "iccssxr.mm"
include "cfz.mm"
include "esumfzf.mm"
include "cvv.mm"
include "ovex.mm"
include "nfcv.mm"
include "nff.mm"
include "nfv.mm"
include "nfan.mm"
include "simpll.mm"
include "1nn.mm"
include "fzssnn.mm"
include "mp1i.mm"
include "simpr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumcl.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "sseldi.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "nnex.mm"
include "ffvelrn.mm"
include "wb.mm"
include "fvelrnb.mm"
include "eqcom.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "rexbidva.mm"
include "bitr4d.mm"
include "biimpa.mm"
include "a1i.mm"
include "adantlr.mm"
include "esummono.mm"
include "adantr.mm"
include "jca.mm"
include "r19.29r.mm"
include "breq1.mm"
include "biimpar.mm"
include "rexlimivw.mm"
include "3syl.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "nfesum1.mm"
include "nfbr.mm"
include "simplll.mm"
include "sylancom.mm"
include "simplr.mm"
include "rexrd.mm"
include "esumlub.mm"
include "ssnnssfz.mm"
include "r19.42v.mm"
include "simp-4l.mm"
include "reximi.mm"
include "sylbir.mm"
include "sylan2.mm"
include "rexbii.mm"
include "sylibr.mm"
include "syl2anc.mm"
include "simp-4r.mm"
include "vex.mm"
include "nfel1.mm"
include "simp-5l.mm"
include "simpllr.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "xrltletr.mm"
include "syl3anc.mm"
include "reximdva.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "breq2d.mm"
include "rexxfr2d.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "supxr2.mm"
include "syl22anc.mm"
include "eqcomd.mm"

theorem esumfsup
  let vk: setvar k
  let cF: class F
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume esumfsup.1: |- F/_ k F


  assert |- ( F : NN --> ( 0 [,] +oo ) -> sum* k e. NN ( F ` k ) = sup ( ran seq 1 ( +e , F ) , RR* , < ) )

  proof
    cn
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    cxad
    cF
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cn
    vk
    cv
    #
    cF
    cfv
    #
    vk
    cesum
    #
    @1
    @3
    cxr
    wss
    #
    @7
    cxr
    wcel
    vx
    cv
    #
    @7
    cle
    wbr
    #
    vx
    @3
    wral
    @9
    @7
    clt
    wbr
    #
    @9
    vy
    cv
    #
    clt
    wbr
    #
    vy
    @3
    wrex
    #
    wi
    #
    vx
    cr
    wral
    @4
    @7
    wceq
    @1
    @2
    cn
    wfn
    #
    vn
    cv
    #
    @2
    cfv
    #
    cxr
    wcel
    #
    vn
    cn
    wral
    @8
    @16
    @2
    c1
    cuz
    cfv
    #
    wfn
    #
    c1
    cz
    wcel
    @21
    1z
    cxad
    cF
    c1
    seqfn
    ax-mp
    cn
    @20
    @2
    nnuz
    fneq2i
    mpbir
    #
    @1
    @19
    vn
    cn
    @1
    @17
    cn
    wcel
    #
    wa
    #
    @0
    cxr
    @18
    cc0
    cpnf
    iccssxr
    #
    @24
    c1
    @17
    cfz
    co
    #
    @6
    vk
    cesum
    #
    @18
    @0
    vk
    cF
    @17
    esumfsup.1
    esumfzf
    #
    @24
    @26
    cvv
    wcel
    #
    @6
    @0
    wcel
    #
    vk
    @26
    wral
    #
    @27
    @0
    wcel
    #
    c1
    @17
    cfz
    ovex
    #
    @24
    @30
    vk
    @26
    @1
    @23
    vk
    vk
    cn
    @0
    cF
    esumfsup.1
    vk
    cn
    nfcv
    #
    vk
    @0
    nfcv
    nff
    #
    @23
    vk
    nfv
    #
    nfan
    #
    @24
    @5
    @26
    wcel
    #
    @30
    @24
    @38
    wa
    #
    cn
    @0
    @5
    cF
    @1
    @23
    @38
    simpll
    @39
    @26
    cn
    @5
    c1
    cn
    wcel
    #
    @26
    cn
    wss
    #
    @39
    1nn
    c1
    @17
    fzssnn
    #
    mp1i
    @24
    @38
    simpr
    sseldd
    ffvelrnd
    ex
    ralrimi
    @26
    @6
    vk
    cvv
    vk
    @26
    nfcv
    esumcl
    #
    sylancr
    #
    eqeltrrd
    sseldi
    ralrimiva
    vn
    cn
    cxr
    @2
    fnfvrnss
    sylancr
    @1
    @0
    cxr
    @7
    @25
    @1
    cn
    cvv
    wcel
    #
    @30
    vk
    cn
    wral
    @7
    @0
    wcel
    nnex
    @1
    @30
    vk
    cn
    @35
    @1
    @5
    cn
    wcel
    #
    @30
    cn
    @0
    @5
    cF
    ffvelrn
    #
    ex
    ralrimi
    cn
    @6
    vk
    cvv
    @34
    esumcl
    sylancr
    sseldi
    @1
    @10
    vx
    @3
    @1
    @9
    @3
    wcel
    #
    wa
    #
    @9
    @27
    wceq
    #
    vn
    cn
    wrex
    #
    @27
    @7
    cle
    wbr
    #
    vn
    cn
    wral
    #
    wa
    @50
    @52
    wa
    #
    vn
    cn
    wrex
    @10
    @49
    @51
    @53
    @1
    @48
    @51
    @1
    @48
    @18
    @9
    wceq
    #
    vn
    cn
    wrex
    #
    @51
    @16
    @48
    @56
    wb
    @1
    @22
    vn
    cn
    @9
    @2
    fvelrnb
    mp1i
    @1
    @50
    @55
    vn
    cn
    @50
    @27
    @9
    wceq
    @24
    @55
    @27
    @9
    eqcom
    @24
    @27
    @18
    @9
    @28
    eqeq1d
    syl5bbr
    rexbidva
    bitr4d
    biimpa
    @1
    @53
    @48
    @1
    @52
    vn
    cn
    @24
    @26
    @6
    cn
    vk
    cvv
    @37
    @45
    @24
    nnex
    a1i
    @1
    @46
    @30
    @23
    @47
    adantlr
    @40
    @41
    @24
    1nn
    @42
    mp1i
    esummono
    ralrimiva
    adantr
    jca
    @50
    @52
    vn
    cn
    r19.29r
    @54
    @10
    vn
    cn
    @50
    @10
    @52
    @9
    @27
    @7
    cle
    breq1
    biimpar
    rexlimivw
    3syl
    ralrimiva
    @1
    @15
    vx
    cr
    @1
    @9
    cr
    wcel
    #
    wa
    #
    @11
    @14
    @58
    @11
    wa
    #
    @14
    @9
    @27
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @59
    @9
    va
    cv
    #
    @6
    vk
    cesum
    #
    clt
    wbr
    #
    @63
    @27
    cle
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    va
    cn
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @61
    @59
    @64
    va
    @69
    wrex
    #
    @65
    vn
    cn
    wrex
    #
    va
    @69
    wral
    #
    @70
    @59
    cn
    @6
    vk
    cvv
    @9
    va
    @58
    @11
    vk
    @1
    @57
    vk
    @35
    @57
    vk
    nfv
    nfan
    vk
    @9
    @7
    clt
    vk
    @9
    nfcv
    vk
    clt
    nfcv
    cn
    @6
    vk
    @34
    nfesum1
    nfbr
    nfan
    #
    @45
    @59
    nnex
    a1i
    @59
    @46
    @1
    @30
    @1
    @57
    @11
    @46
    simplll
    @47
    sylancom
    @59
    @9
    @1
    @57
    @11
    simplr
    rexrd
    @58
    @11
    simpr
    esumlub
    @59
    @72
    va
    @69
    @62
    @69
    wcel
    #
    @59
    @62
    @26
    wss
    #
    vn
    cn
    wrex
    #
    @72
    @62
    vn
    ssnnssfz
    @59
    @77
    wa
    @59
    @76
    wa
    #
    vn
    cn
    wrex
    @72
    @59
    @76
    vn
    cn
    r19.42v
    @78
    @65
    vn
    cn
    @78
    @62
    @6
    @26
    vk
    cvv
    @59
    @76
    vk
    @74
    @76
    vk
    nfv
    nfan
    @29
    @78
    @33
    a1i
    @78
    @38
    wa
    #
    cn
    @0
    @5
    cF
    @1
    @57
    @11
    @76
    @38
    simp-4l
    @79
    @26
    cn
    @5
    @40
    @41
    1nn
    @42
    ax-mp
    #
    @78
    @38
    simpr
    sseldi
    ffvelrnd
    @59
    @76
    simpr
    esummono
    reximi
    sylbir
    sylan2
    ralrimiva
    @71
    @73
    wa
    @64
    @72
    wa
    #
    va
    @69
    wrex
    @70
    @64
    @72
    va
    @69
    r19.29r
    @67
    @81
    va
    @69
    @64
    @65
    vn
    cn
    r19.42v
    rexbii
    sylibr
    syl2anc
    @59
    @67
    @61
    va
    @69
    @59
    @75
    wa
    #
    @66
    @60
    vn
    cn
    @82
    @23
    wa
    #
    @9
    cxr
    wcel
    @63
    cxr
    wcel
    @27
    cxr
    wcel
    @66
    @60
    wi
    @83
    @9
    @1
    @57
    @11
    @75
    @23
    simp-4r
    rexrd
    @83
    @0
    cxr
    @63
    @25
    @83
    @62
    cvv
    wcel
    @30
    vk
    @62
    wral
    @63
    @0
    wcel
    va
    vex
    @83
    @30
    vk
    @62
    @82
    @23
    vk
    @59
    @75
    vk
    @74
    vk
    @62
    @69
    vk
    @62
    nfcv
    #
    nfel1
    nfan
    @36
    nfan
    #
    @83
    @5
    @62
    wcel
    #
    @30
    @83
    @86
    wa
    #
    cn
    @0
    @5
    cF
    @1
    @57
    @11
    @75
    @23
    @86
    simp-5l
    @87
    @62
    cn
    @5
    @87
    @75
    @62
    @68
    wcel
    @62
    cn
    wss
    @59
    @75
    @23
    @86
    simpllr
    @69
    @68
    @62
    @68
    cfn
    inss1
    sseli
    @62
    cn
    elpwi
    3syl
    @83
    @86
    simpr
    sseldd
    ffvelrnd
    ex
    ralrimi
    @62
    @6
    vk
    cvv
    @84
    esumcl
    sylancr
    sseldi
    @83
    @0
    cxr
    @27
    @25
    @83
    @29
    @31
    @32
    @33
    @83
    @30
    vk
    @26
    @85
    @83
    @38
    @30
    @83
    @38
    wa
    #
    cn
    @0
    @5
    cF
    @1
    @57
    @11
    @75
    @23
    @38
    simp-5l
    @88
    @26
    cn
    @5
    @80
    @83
    @38
    simpr
    sseldi
    ffvelrnd
    ex
    ralrimi
    @43
    sylancr
    sseldi
    @9
    @63
    @27
    xrltletr
    syl3anc
    reximdva
    rexlimdva
    mpd
    @1
    @14
    @61
    wb
    @57
    @11
    @1
    @13
    @60
    vy
    vn
    @27
    @3
    cn
    @0
    @44
    @1
    @12
    @3
    wcel
    #
    @18
    @12
    wceq
    #
    vn
    cn
    wrex
    #
    @12
    @27
    wceq
    #
    vn
    cn
    wrex
    @16
    @89
    @91
    wb
    @1
    @22
    vn
    cn
    @12
    @2
    fvelrnb
    mp1i
    @1
    @92
    @90
    vn
    cn
    @92
    @27
    @12
    wceq
    @24
    @90
    @27
    @12
    eqcom
    @24
    @27
    @18
    @12
    @28
    eqeq1d
    syl5bbr
    rexbidva
    bitr4d
    @1
    @92
    wa
    @12
    @27
    @9
    clt
    @1
    @92
    simpr
    breq2d
    rexxfr2d
    ad2antrr
    mpbird
    ex
    ralrimiva
    vx
    vy
    @3
    @7
    supxr2
    syl22anc
    eqcomd
end
