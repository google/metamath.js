include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cioo.mm"
include "wa.mm"
include "c1.mm"
include "ctan.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "cmin.mm"
include "cabs.mm"
include "cexp.mm"
include "ccj.mm"
include "caddc.mm"
include "clt.mm"
include "crp.mm"
include "cz.mm"
include "ax-1cn.mm"
include "cr.mm"
include "recl.mm"
include "adantr.mm"
include "recnd.mm"
include "cneg.mm"
include "ccos.mm"
include "wne.mm"
include "rered.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "neghalfpire.mm"
include "rexri.mm"
include "0re.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpgt0.mm"
include "mp2b.mm"
include "wb.mm"
include "halfpire.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "ltleii.mm"
include "iooss1.mm"
include "mp2an.mm"
include "simpr.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "cosne0.mm"
include "syl2anc.mm"
include "tancld.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "rpcoshcl.mm"
include "syl.mm"
include "rpne0d.mm"
include "mulcld.mm"
include "subcl.mm"
include "wceq.mm"
include "replim.mm"
include "fveq2d.mm"
include "syldan.mm"
include "eqnetrrd.mm"
include "tanaddlem.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "necomd.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "absrpcld.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rprecred.mm"
include "cjcld.mm"
include "addcld.mm"
include "recld.mm"
include "rpreccld.mm"
include "rpgt0d.mm"
include "retancld.mm"
include "1re.mm"
include "retanhcl.mm"
include "resqcld.mm"
include "resubcl.mm"
include "tanrpcl.mm"
include "adantl.mm"
include "absresq.mm"
include "tanhbnd.mm"
include "eliooord.mm"
include "abslt.mm"
include "abscld.mm"
include "a1i.mm"
include "absge0d.mm"
include "0le1.mm"
include "lt2sqd.mm"
include "sq1.mm"
include "syl6breq.mm"
include "eqbrtrrd.mm"
include "posdif.mm"
include "mulgt0d.mm"
include "recjd.mm"
include "resub.mm"
include "re1.mm"
include "oveq1i.mm"
include "remul2d.mm"
include "negicn.mm"
include "ine0.mm"
include "negne0i.mm"
include "divcld.mm"
include "imre.mm"
include "divneg2d.mm"
include "renegcld.mm"
include "eqeltrrd.mm"
include "reim0d.mm"
include "divcan2d.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "3eqtrd.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "crred.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "mulcom.mm"
include "eqtrd.mm"
include "mulassd.mm"
include "imcjd.mm"
include "imsub.mm"
include "im1.mm"
include "df-neg.mm"
include "eqtr4i.mm"
include "immul2d.mm"
include "imval.mm"
include "negeqd.mm"
include "remulcld.mm"
include "negnegd.mm"
include "crimd.mm"
include "sqvald.mm"
include "3eqtr4d.mm"
include "remuld.mm"
include "sqcld.mm"
include "subdid.mm"
include "breqtrrd.mm"
include "tanadd.mm"
include "syl23anc.mm"
include "recval.mm"
include "oveq1d.mm"
include "divrec2d.mm"
include "div23d.mm"

theorem tanregt0
  let cA: class A


  assert |- ( ( A e. CC /\ ( Re ` A ) e. ( 0 (,) ( _pi / 2 ) ) ) -> 0 < ( Re ` ( tan ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cre
    cfv
    #
    cc0
    cpi
    c2
    cdiv
    co
    #
    cioo
    co
    #
    wcel
    #
    wa
    #
    cc0
    c1
    c1
    @1
    ctan
    cfv
    #
    ci
    cA
    cim
    cfv
    #
    cmul
    co
    #
    ctan
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @11
    ccj
    cfv
    #
    @6
    @9
    caddc
    co
    #
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    cA
    ctan
    cfv
    #
    cre
    cfv
    #
    clt
    @5
    @14
    @18
    @5
    @13
    @5
    @12
    crp
    wcel
    c2
    cz
    wcel
    @13
    crp
    wcel
    @5
    @11
    @5
    c1
    cc
    wcel
    #
    @10
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    ax-1cn
    @5
    @6
    @9
    @5
    @1
    @5
    @1
    @0
    @1
    cr
    wcel
    @4
    cA
    recl
    adantr
    #
    recnd
    #
    @5
    @1
    cc
    wcel
    #
    @1
    cre
    cfv
    #
    @2
    cneg
    #
    @2
    cioo
    co
    #
    wcel
    @1
    ccos
    cfv
    cc0
    wne
    #
    @26
    @5
    @28
    @1
    @30
    @5
    @1
    @25
    rered
    @5
    @3
    @30
    @1
    @29
    cxr
    wcel
    @29
    cc0
    cle
    wbr
    @3
    @30
    wss
    @29
    neghalfpire
    rexri
    @29
    cc0
    neghalfpire
    0re
    cc0
    @2
    clt
    wbr
    #
    @29
    cc0
    clt
    wbr
    #
    cpi
    crp
    wcel
    @2
    crp
    wcel
    @32
    pirp
    cpi
    rphalfcl
    @2
    rpgt0
    mp2b
    @2
    cr
    wcel
    @32
    @33
    wb
    halfpire
    @2
    lt0neg2
    ax-mp
    mpbi
    ltleii
    @29
    cc0
    @2
    iooss1
    mp2an
    @0
    @4
    simpr
    sseldi
    #
    eqeltrd
    @1
    cosne0
    syl2anc
    #
    tancld
    #
    @5
    @8
    @5
    ci
    cc
    wcel
    #
    @7
    cc
    wcel
    @8
    cc
    wcel
    #
    ax-icn
    @5
    @7
    @0
    @7
    cr
    wcel
    #
    @4
    cA
    imcl
    adantr
    #
    recnd
    ci
    @7
    mulcl
    sylancr
    #
    @5
    @8
    ccos
    cfv
    #
    @5
    @39
    @42
    crp
    wcel
    @40
    @7
    rpcoshcl
    syl
    rpne0d
    #
    tancld
    #
    mulcld
    #
    c1
    @10
    subcl
    sylancr
    #
    @5
    @11
    cc0
    wne
    #
    c1
    @10
    wne
    #
    @5
    @10
    c1
    @5
    @1
    @8
    caddc
    co
    #
    ccos
    cfv
    #
    cc0
    wne
    #
    @10
    c1
    wne
    #
    @5
    cA
    ccos
    cfv
    #
    @50
    cc0
    @5
    cA
    @49
    ccos
    @0
    cA
    @49
    wceq
    @4
    cA
    replim
    adantr
    #
    fveq2d
    @0
    @4
    @1
    @30
    wcel
    @53
    cc0
    wne
    @34
    cA
    cosne0
    syldan
    eqnetrrd
    #
    @5
    @27
    @38
    @31
    @42
    cc0
    wne
    #
    @51
    @52
    wb
    @26
    @41
    @35
    @43
    @1
    @8
    tanaddlem
    syl22anc
    mpbid
    necomd
    @5
    @22
    @23
    @47
    @48
    wb
    ax-1cn
    @45
    @22
    @23
    wa
    @11
    cc0
    c1
    @10
    c1
    @10
    subeq0
    necon3bid
    sylancr
    mpbird
    #
    absrpcld
    2z
    @12
    c2
    rpexpcl
    sylancl
    #
    rprecred
    #
    @5
    @17
    @5
    @15
    @16
    @5
    @11
    @46
    cjcld
    #
    @5
    @6
    @9
    @36
    @44
    addcld
    #
    mulcld
    #
    recld
    @5
    @14
    @5
    @13
    @58
    rpreccld
    rpgt0d
    @5
    cc0
    @6
    c1
    @9
    ci
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    @18
    clt
    @5
    @6
    @65
    @5
    @1
    @25
    @35
    retancld
    #
    @5
    c1
    cr
    wcel
    #
    @64
    cr
    wcel
    #
    @65
    cr
    wcel
    1re
    @5
    @63
    @5
    @39
    @63
    cr
    wcel
    #
    @40
    @7
    retanhcl
    syl
    #
    resqcld
    #
    c1
    @64
    resubcl
    sylancr
    @5
    @6
    @4
    @6
    crp
    wcel
    @0
    @1
    tanrpcl
    adantl
    rpgt0d
    @5
    @64
    c1
    clt
    wbr
    #
    cc0
    @65
    clt
    wbr
    #
    @5
    @63
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @64
    c1
    clt
    @5
    @70
    @76
    @64
    wceq
    @71
    @63
    absresq
    syl
    @5
    @76
    c1
    c2
    cexp
    co
    #
    c1
    clt
    @5
    @75
    c1
    clt
    wbr
    #
    @76
    @77
    clt
    wbr
    @5
    @78
    c1
    cneg
    #
    @63
    clt
    wbr
    @63
    c1
    clt
    wbr
    wa
    #
    @5
    @63
    @79
    c1
    cioo
    co
    wcel
    #
    @80
    @5
    @39
    @81
    @40
    @7
    tanhbnd
    syl
    @63
    @79
    c1
    eliooord
    syl
    @5
    @70
    @68
    @78
    @80
    wb
    @71
    1re
    @63
    c1
    abslt
    sylancl
    mpbird
    @5
    @75
    c1
    @5
    @63
    @5
    @63
    @71
    recnd
    #
    abscld
    @68
    @5
    1re
    a1i
    @5
    @63
    @82
    absge0d
    cc0
    c1
    cle
    wbr
    @5
    0le1
    a1i
    lt2sqd
    mpbid
    sq1
    syl6breq
    eqbrtrrd
    @5
    @69
    @68
    @73
    @74
    wb
    @72
    1re
    @64
    c1
    posdif
    sylancl
    mpbid
    mulgt0d
    @5
    @15
    cre
    cfv
    #
    @16
    cre
    cfv
    #
    cmul
    co
    #
    @15
    cim
    cfv
    #
    @16
    cim
    cfv
    #
    cmul
    co
    #
    cmin
    co
    @6
    c1
    cmul
    co
    #
    @6
    @64
    cmul
    co
    #
    cmin
    co
    @18
    @66
    @5
    @85
    @89
    @88
    @90
    cmin
    @5
    @85
    c1
    @6
    cmul
    co
    #
    @89
    @5
    @83
    c1
    @84
    @6
    cmul
    @5
    @83
    @11
    cre
    cfv
    #
    c1
    cre
    cfv
    #
    @10
    cre
    cfv
    #
    cmin
    co
    #
    c1
    @5
    @11
    @46
    recjd
    @5
    @22
    @23
    @92
    @95
    wceq
    ax-1cn
    @45
    c1
    @10
    resub
    sylancr
    @5
    @95
    c1
    @94
    cmin
    co
    #
    c1
    @93
    c1
    @94
    cmin
    re1
    oveq1i
    @5
    @96
    c1
    cc0
    cmin
    co
    c1
    @5
    @94
    cc0
    c1
    cmin
    @5
    @94
    @6
    @9
    cre
    cfv
    #
    cmul
    co
    @6
    cc0
    cmul
    co
    cc0
    @5
    @6
    @9
    @67
    @44
    remul2d
    @5
    @97
    cc0
    @6
    cmul
    @5
    @9
    ci
    cneg
    #
    cdiv
    co
    #
    cim
    cfv
    #
    @98
    @99
    cmul
    co
    #
    cre
    cfv
    #
    cc0
    @97
    @5
    @99
    cc
    wcel
    @100
    @102
    wceq
    @5
    @9
    @98
    @44
    @98
    cc
    wcel
    @5
    negicn
    a1i
    #
    @98
    cc0
    wne
    @5
    ci
    ax-icn
    ine0
    negne0i
    a1i
    #
    divcld
    @99
    imre
    syl
    @5
    @99
    @5
    @63
    cneg
    @99
    cr
    @5
    @9
    ci
    @44
    @37
    @5
    ax-icn
    a1i
    #
    ci
    cc0
    wne
    @5
    ine0
    a1i
    #
    divneg2d
    @5
    @63
    @71
    renegcld
    eqeltrrd
    reim0d
    @5
    @101
    @9
    cre
    @5
    @9
    @98
    @44
    @103
    @104
    divcan2d
    fveq2d
    3eqtr3rd
    oveq2d
    @5
    @6
    @36
    mul01d
    3eqtrd
    oveq2d
    1m0e1
    syl6eq
    syl5eq
    3eqtrd
    @5
    @6
    ci
    @63
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    @84
    @6
    @5
    @108
    @16
    cre
    @5
    @107
    @9
    @6
    caddc
    @5
    @9
    ci
    @44
    @105
    @106
    divcan2d
    oveq2d
    #
    fveq2d
    @5
    @6
    @63
    @67
    @71
    crred
    eqtr3d
    oveq12d
    @5
    @22
    @6
    cc
    wcel
    @91
    @89
    wceq
    ax-1cn
    @36
    c1
    @6
    mulcom
    sylancr
    eqtrd
    @5
    @6
    @63
    cmul
    co
    #
    @63
    cmul
    co
    @6
    @63
    @63
    cmul
    co
    #
    cmul
    co
    @88
    @90
    @5
    @6
    @63
    @63
    @36
    @82
    @82
    mulassd
    @5
    @86
    @110
    @87
    @63
    cmul
    @5
    @86
    @11
    cim
    cfv
    #
    cneg
    @110
    cneg
    #
    cneg
    @110
    @5
    @11
    @46
    imcjd
    @5
    @112
    @113
    @5
    @112
    c1
    cim
    cfv
    #
    @10
    cim
    cfv
    #
    cmin
    co
    #
    @113
    @5
    @22
    @23
    @112
    @116
    wceq
    ax-1cn
    @45
    c1
    @10
    imsub
    sylancr
    @5
    @116
    @115
    cneg
    #
    @113
    @116
    cc0
    @115
    cmin
    co
    @117
    @114
    cc0
    @115
    cmin
    im1
    oveq1i
    @115
    df-neg
    eqtr4i
    @5
    @115
    @110
    @5
    @115
    @6
    @9
    cim
    cfv
    #
    cmul
    co
    @110
    @5
    @6
    @9
    @67
    @44
    immul2d
    @5
    @118
    @63
    @6
    cmul
    @5
    @118
    @63
    cre
    cfv
    #
    @63
    @5
    @9
    cc
    wcel
    @118
    @119
    wceq
    @44
    @9
    imval
    syl
    @5
    @63
    @71
    rered
    eqtrd
    oveq2d
    eqtrd
    negeqd
    syl5eq
    eqtrd
    negeqd
    @5
    @110
    @5
    @110
    @5
    @6
    @63
    @67
    @71
    remulcld
    recnd
    negnegd
    3eqtrd
    @5
    @108
    cim
    cfv
    @87
    @63
    @5
    @108
    @16
    cim
    @109
    fveq2d
    @5
    @6
    @63
    @67
    @71
    crimd
    eqtr3d
    oveq12d
    @5
    @64
    @111
    @6
    cmul
    @5
    @63
    @82
    sqvald
    oveq2d
    3eqtr4d
    oveq12d
    @5
    @15
    @16
    @60
    @61
    remuld
    @5
    @6
    c1
    @64
    @36
    @22
    @5
    ax-1cn
    a1i
    @5
    @63
    @82
    sqcld
    subdid
    3eqtr4d
    breqtrrd
    mulgt0d
    @5
    @21
    @14
    @17
    cmul
    co
    #
    cre
    cfv
    @19
    @5
    @20
    @120
    cre
    @5
    @20
    @17
    @13
    cdiv
    co
    #
    @120
    @5
    @20
    @49
    ctan
    cfv
    #
    @16
    @11
    cdiv
    co
    #
    @121
    @5
    cA
    @49
    ctan
    @54
    fveq2d
    @5
    @27
    @38
    @31
    @56
    @51
    @122
    @123
    wceq
    @26
    @41
    @35
    @43
    @55
    @1
    @8
    tanadd
    syl23anc
    @5
    c1
    @11
    cdiv
    co
    #
    @16
    cmul
    co
    @15
    @13
    cdiv
    co
    #
    @16
    cmul
    co
    @123
    @121
    @5
    @124
    @125
    @16
    cmul
    @5
    @24
    @47
    @124
    @125
    wceq
    @46
    @57
    @11
    recval
    syl2anc
    oveq1d
    @5
    @16
    @11
    @61
    @46
    @57
    divrec2d
    @5
    @15
    @16
    @13
    @60
    @61
    @5
    @13
    @5
    @12
    @5
    @11
    @46
    abscld
    resqcld
    recnd
    #
    @5
    @13
    @58
    rpne0d
    #
    div23d
    3eqtr4d
    3eqtrd
    @5
    @17
    @13
    @62
    @126
    @127
    divrec2d
    eqtrd
    fveq2d
    @5
    @14
    @17
    @59
    @62
    remul2d
    eqtrd
    breqtrrd
end
