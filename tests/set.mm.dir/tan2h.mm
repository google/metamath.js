include "cc0.mm"
include "cpi.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "ctan.mm"
include "cfv.mm"
include "c1.mm"
include "ccos.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "csin.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "cr.mm"
include "cxr.mm"
include "wss.mm"
include "0re.mm"
include "pire.mm"
include "rexri.mm"
include "icossre.mm"
include "mp2an.mm"
include "sseli.mm"
include "recnd.mm"
include "halfcld.mm"
include "cre.mm"
include "cneg.mm"
include "cioo.mm"
include "rehalfcld.mm"
include "rered.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "w3a.mm"
include "wb.mm"
include "elico2.mm"
include "wa.mm"
include "pipos.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "wi.mm"
include "renegcli.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltdiv1.mm"
include "mp3an13.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "mp3an.mm"
include "breq1i.mm"
include "syl6bbr.mm"
include "sylibd.mm"
include "mp3an23.mm"
include "biimpd.mm"
include "anim12d.mm"
include "rehalfcl.mm"
include "rexrd.mm"
include "halfpire.mm"
include "elioo5.mm"
include "syl.mm"
include "sylibrd.mm"
include "3impib.mm"
include "sylbi.mm"
include "eqeltrd.mm"
include "cosne0.mm"
include "syl2anc.mm"
include "tanval.mm"
include "cmul.mm"
include "cicc.mm"
include "0xr.mm"
include "elico1.mm"
include "remulcli.mm"
include "1lt2.mm"
include "ltmulgt12.mm"
include "xrlttr.mm"
include "mp3an2.mm"
include "mpan2i.mm"
include "xrltle.mm"
include "syld.mm"
include "mpan2.mm"
include "anim2d.mm"
include "elicc4.mm"
include "sin2h.mm"
include "ltleii.mm"
include "le0neg2.mm"
include "xrletr.mm"
include "cos2h.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "1re.mm"
include "recoscld.mm"
include "resubcl.mm"
include "sylancr.mm"
include "cosbnd.mm"
include "simprd.mm"
include "recoscl.mm"
include "subge0.mm"
include "halfnneg2.mm"
include "bitr3d.mm"
include "mpbid.mm"
include "readdcl.mm"
include "simpld.mm"
include "sylancl.mm"
include "recn.mm"
include "coscld.mm"
include "ax-1cn.mm"
include "subneg.mm"
include "addcom.mm"
include "breq2d.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "snunioo.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "elsni.mm"
include "fveq2.mm"
include "cos0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "df-2.mm"
include "syl6eqr.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "sinq12gt0.mm"
include "ltne.mm"
include "mpan.mm"
include "elioore.mm"
include "cexp.mm"
include "oveq1.mm"
include "df-neg.mm"
include "eqeq1i.mm"
include "coscl.mm"
include "0cn.mm"
include "subadd.mm"
include "syl5bb.mm"
include "sincl.mm"
include "sqcld.mm"
include "0cnd.mm"
include "addcan2d.mm"
include "sincossq.mm"
include "neg1sqe1.mm"
include "addid2d.mm"
include "eqeq12d.mm"
include "sqeq0.mm"
include "3bitr3d.mm"
include "3imtr3d.mm"
include "necon3d.mm"
include "syl5.mm"
include "mpd.mm"
include "jaoi.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "sqrtdivd.mm"
include "subcl.mm"
include "addcl.mm"
include "2cnne0.mm"
include "divcan7.mm"
include "mp3an3.mm"
include "syl12anc.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"

theorem tan2h
  let cA: class A


  assert |- ( A e. ( 0 [,) _pi ) -> ( tan ` ( A / 2 ) ) = ( sqrt ` ( ( 1 - ( cos ` A ) ) / ( 1 + ( cos ` A ) ) ) ) )

  proof
    cA
    cc0
    cpi
    cico
    co
    #
    wcel
    #
    cA
    c2
    cdiv
    co
    #
    ctan
    cfv
    #
    c1
    cA
    ccos
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    csqrt
    cfv
    #
    c1
    @4
    caddc
    co
    #
    c2
    cdiv
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    @6
    @9
    cdiv
    co
    #
    csqrt
    cfv
    @5
    @8
    cdiv
    co
    #
    csqrt
    cfv
    @1
    @3
    @2
    csin
    cfv
    #
    @2
    ccos
    cfv
    #
    cdiv
    co
    #
    @11
    @1
    @2
    cc
    wcel
    #
    @15
    cc0
    wne
    #
    @3
    @16
    wceq
    @1
    cA
    @1
    cA
    @0
    cr
    cA
    cc0
    cr
    wcel
    #
    cpi
    cxr
    wcel
    #
    @0
    cr
    wss
    0re
    cpi
    pire
    rexri
    #
    cc0
    cpi
    icossre
    mp2an
    sseli
    #
    recnd
    #
    halfcld
    #
    @1
    @17
    @2
    cre
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @26
    cioo
    co
    #
    wcel
    @18
    @24
    @1
    @25
    @2
    @28
    @1
    @2
    @1
    cA
    @22
    rehalfcld
    rered
    @1
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cpi
    clt
    wbr
    #
    w3a
    #
    @2
    @28
    wcel
    #
    @19
    @20
    @1
    @32
    wb
    0re
    @21
    cc0
    cpi
    cA
    elico2
    mp2an
    @29
    @30
    @31
    @33
    @29
    @30
    @31
    wa
    #
    @27
    @2
    clt
    wbr
    #
    @2
    @26
    clt
    wbr
    #
    wa
    #
    @33
    @29
    @30
    @35
    @31
    @36
    @29
    @30
    cpi
    cneg
    #
    cA
    clt
    wbr
    #
    @35
    @29
    @38
    cc0
    clt
    wbr
    #
    @30
    @39
    cc0
    cpi
    clt
    wbr
    #
    @40
    pipos
    cpi
    cr
    wcel
    #
    @41
    @40
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    @38
    cr
    wcel
    #
    @19
    @29
    @40
    @30
    wa
    @39
    wi
    cpi
    pire
    renegcli
    #
    0re
    @38
    cc0
    cA
    ltletr
    mp3an12
    mpani
    @29
    @39
    @38
    c2
    cdiv
    co
    #
    @2
    clt
    wbr
    #
    @35
    @43
    @29
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @39
    @46
    wb
    @44
    @47
    @48
    2re
    2pos
    pm3.2i
    #
    @38
    cA
    c2
    ltdiv1
    mp3an13
    @27
    @45
    @2
    clt
    cpi
    cc
    wcel
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @27
    @45
    wceq
    picn
    2cn
    2ne0
    cpi
    c2
    divneg
    mp3an
    breq1i
    syl6bbr
    sylibd
    @29
    @31
    @36
    @29
    @42
    @49
    @31
    @36
    wb
    pire
    @50
    cA
    cpi
    c2
    ltdiv1
    mp3an23
    biimpd
    anim12d
    @29
    @2
    cxr
    wcel
    #
    @33
    @37
    wb
    #
    @29
    @2
    cA
    rehalfcl
    rexrd
    @27
    cxr
    wcel
    @26
    cxr
    wcel
    @53
    @54
    @27
    @26
    halfpire
    renegcli
    rexri
    @26
    halfpire
    rexri
    @27
    @26
    @2
    elioo5
    mp3an12
    syl
    sylibrd
    3impib
    sylbi
    eqeltrd
    @2
    cosne0
    syl2anc
    @2
    tanval
    syl2anc
    @1
    @14
    @7
    @15
    @10
    cdiv
    @1
    cA
    cc0
    c2
    cpi
    cmul
    co
    #
    cicc
    co
    wcel
    #
    @14
    @7
    wceq
    @1
    cA
    cxr
    wcel
    #
    @30
    @31
    w3a
    #
    @56
    cc0
    cxr
    wcel
    #
    @20
    @1
    @58
    wb
    0xr
    @21
    cc0
    cpi
    cA
    elico1
    mp2an
    #
    @57
    @30
    @31
    @56
    @57
    @34
    @30
    cA
    @55
    cle
    wbr
    #
    wa
    #
    @56
    @57
    @31
    @61
    @30
    @57
    @55
    cxr
    wcel
    #
    @31
    @61
    wi
    @55
    c2
    cpi
    2re
    pire
    remulcli
    rexri
    #
    @57
    @63
    wa
    #
    @31
    cA
    @55
    clt
    wbr
    #
    @61
    @65
    @31
    cpi
    @55
    clt
    wbr
    #
    @66
    c1
    c2
    clt
    wbr
    #
    @67
    1lt2
    @42
    @47
    @41
    @68
    @67
    wb
    pire
    2re
    pipos
    cpi
    c2
    ltmulgt12
    mp3an
    mpbi
    @57
    @20
    @63
    @31
    @67
    wa
    @66
    wi
    @21
    cA
    cpi
    @55
    xrlttr
    mp3an2
    mpan2i
    cA
    @55
    xrltle
    syld
    mpan2
    anim2d
    @59
    @63
    @57
    @56
    @62
    wb
    0xr
    @64
    cc0
    @55
    cA
    elicc4
    mp3an12
    sylibrd
    3impib
    sylbi
    cA
    sin2h
    syl
    @1
    cA
    @38
    cpi
    cicc
    co
    wcel
    #
    @15
    @10
    wceq
    @1
    @58
    @69
    @60
    @57
    @30
    @31
    @69
    @57
    @34
    @38
    cA
    cle
    wbr
    #
    cA
    cpi
    cle
    wbr
    #
    wa
    #
    @69
    @57
    @30
    @70
    @31
    @71
    @57
    @38
    cc0
    cle
    wbr
    #
    @30
    @70
    cc0
    cpi
    cle
    wbr
    #
    @73
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    @42
    @74
    @73
    wb
    pire
    cpi
    le0neg2
    ax-mp
    mpbi
    @38
    cxr
    wcel
    #
    @59
    @57
    @73
    @30
    wa
    @70
    wi
    @38
    @44
    rexri
    #
    0xr
    @38
    cc0
    cA
    xrletr
    mp3an12
    mpani
    @57
    @20
    @31
    @71
    wi
    @21
    cA
    cpi
    xrltle
    mpan2
    anim12d
    @75
    @20
    @57
    @69
    @72
    wb
    @76
    @21
    @38
    cpi
    cA
    elicc4
    mp3an12
    sylibrd
    3impib
    sylbi
    cA
    cos2h
    syl
    oveq12d
    eqtrd
    @1
    @6
    @9
    @1
    @5
    @1
    c1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    1re
    @1
    cA
    @22
    recoscld
    #
    c1
    @4
    resubcl
    #
    sylancr
    rehalfcld
    @1
    @29
    cc0
    @6
    cle
    wbr
    #
    @22
    @29
    @4
    c1
    cle
    wbr
    #
    @82
    @29
    c1
    cneg
    #
    @4
    cle
    wbr
    #
    @83
    cA
    cosbnd
    #
    simprd
    @29
    @77
    @78
    @83
    @82
    wb
    1re
    cA
    recoscl
    #
    @77
    @78
    wa
    #
    cc0
    @5
    cle
    wbr
    #
    @83
    @82
    c1
    @4
    subge0
    @88
    @79
    @89
    @82
    wb
    @81
    @5
    halfnneg2
    syl
    bitr3d
    sylancr
    mpbid
    syl
    @1
    @8
    @1
    @8
    @1
    @77
    @78
    @8
    cr
    wcel
    1re
    @80
    c1
    @4
    readdcl
    sylancr
    #
    @1
    @8
    @90
    @1
    @29
    cc0
    @8
    cle
    wbr
    #
    @22
    @29
    @85
    @91
    @29
    @85
    @83
    @86
    simpld
    @29
    cc0
    @4
    @84
    cmin
    co
    #
    cle
    wbr
    #
    @85
    @91
    @29
    @78
    @84
    cr
    wcel
    @93
    @85
    wb
    @87
    c1
    1re
    renegcli
    @4
    @84
    subge0
    sylancl
    @29
    @92
    @8
    cc0
    cle
    @29
    @4
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @92
    @8
    wceq
    @29
    cA
    cA
    recn
    coscld
    ax-1cn
    @94
    @95
    wa
    @92
    @4
    c1
    caddc
    co
    @8
    @4
    c1
    subneg
    @4
    c1
    addcom
    eqtrd
    sylancl
    breq2d
    bitr3d
    mpbid
    syl
    @1
    cA
    cc0
    csn
    #
    wcel
    #
    cA
    cc0
    cpi
    cioo
    co
    #
    wcel
    #
    wo
    #
    @8
    cc0
    wne
    #
    @1
    cA
    @96
    @98
    cun
    #
    wcel
    @100
    @102
    @0
    cA
    @59
    @20
    @41
    @102
    @0
    wceq
    0xr
    @21
    pipos
    cc0
    cpi
    snunioo
    mp3an
    eleq2i
    cA
    @96
    @98
    elun
    bitr3i
    @97
    @101
    @99
    @97
    cA
    cc0
    wceq
    #
    @101
    cA
    cc0
    elsni
    @103
    @8
    c2
    cc0
    @103
    @8
    c1
    c1
    caddc
    co
    c2
    @103
    @4
    c1
    c1
    caddc
    @103
    @4
    cc0
    ccos
    cfv
    c1
    cA
    cc0
    ccos
    fveq2
    cos0
    syl6eq
    oveq2d
    df-2
    syl6eqr
    @52
    @103
    2ne0
    a1i
    eqnetrd
    syl
    @99
    cc0
    cA
    csin
    cfv
    #
    clt
    wbr
    #
    @101
    cA
    sinq12gt0
    @105
    @104
    cc0
    wne
    #
    @99
    @101
    @19
    @105
    @106
    0re
    cc0
    @104
    ltne
    mpan
    @99
    @8
    cc0
    @104
    cc0
    @99
    cA
    cc
    wcel
    #
    @8
    cc0
    wceq
    #
    @104
    cc0
    wceq
    #
    wi
    @99
    cA
    cA
    cc0
    cpi
    elioore
    recnd
    @107
    @84
    @4
    wceq
    #
    @84
    c2
    cexp
    co
    #
    @4
    c2
    cexp
    co
    #
    wceq
    #
    @108
    @109
    @110
    @113
    wi
    @107
    @84
    @4
    c2
    cexp
    oveq1
    a1i
    @110
    cc0
    c1
    cmin
    co
    #
    @4
    wceq
    #
    @107
    @108
    @84
    @114
    @4
    c1
    df-neg
    eqeq1i
    @107
    @94
    @115
    @108
    wb
    #
    cA
    coscl
    #
    cc0
    cc
    wcel
    @95
    @94
    @116
    0cn
    ax-1cn
    cc0
    c1
    @4
    subadd
    mp3an12
    syl
    syl5bb
    @107
    @104
    c2
    cexp
    co
    #
    @112
    caddc
    co
    #
    cc0
    @112
    caddc
    co
    #
    wceq
    @118
    cc0
    wceq
    #
    @113
    @109
    @107
    @118
    cc0
    @112
    @107
    @104
    cA
    sincl
    #
    sqcld
    @107
    0cnd
    @107
    @4
    @117
    sqcld
    #
    addcan2d
    @107
    @119
    @111
    @120
    @112
    @107
    @119
    c1
    @111
    cA
    sincossq
    neg1sqe1
    syl6eqr
    @107
    @112
    @123
    addid2d
    eqeq12d
    @107
    @104
    cc
    wcel
    @121
    @109
    wb
    @122
    @104
    sqeq0
    syl
    3bitr3d
    3imtr3d
    syl
    necon3d
    syl5
    mpd
    jaoi
    sylbi
    #
    ne0gt0d
    elrpd
    rphalfcld
    sqrtdivd
    @1
    @12
    @13
    csqrt
    @1
    @5
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @101
    @12
    @13
    wceq
    #
    @1
    @95
    @94
    @125
    ax-1cn
    @1
    cA
    @23
    coscld
    #
    c1
    @4
    subcl
    sylancr
    @1
    @95
    @94
    @126
    ax-1cn
    @128
    c1
    @4
    addcl
    sylancr
    @124
    @125
    @126
    @101
    wa
    @51
    @52
    wa
    @127
    2cnne0
    @5
    @8
    c2
    divcan7
    mp3an3
    syl12anc
    fveq2d
    3eqtr2d
end
