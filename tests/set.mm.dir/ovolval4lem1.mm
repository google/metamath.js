include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "cvol.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "cdif.mm"
include "cun.mm"
include "wfn.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "cxr.mm"
include "cxp.mm"
include "ioof.mm"
include "a1i.mm"
include "fco.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "fniunfv.mm"
include "eqcomd.mm"
include "wss.mm"
include "c1st.mm"
include "c2nd.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "undif.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "iuneq1i.mm"
include "iunxun.mm"
include "eqtri.mm"
include "cif.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "ifcld.mm"
include "opelxpd.mm"
include "fmptd.mm"
include "adantr.mm"
include "sseli.mm"
include "adantl.mm"
include "fvco3.mm"
include "simpl.mm"
include "1st2nd2.mm"
include "cvv.mm"
include "cmpt.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "iftrued.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "iuneq2dv.mm"
include "c0.mm"
include "eldifi.mm"
include "anim1i.mm"
include "sylibr.mm"
include "adantll.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "pm2.65da.mm"
include "iffalsed.mm"
include "co.mm"
include "iooid.mm"
include "df-ov.mm"
include "eqtr2i.mm"
include "iun0.mm"
include "simplr.mm"
include "syldan.mm"
include "clt.mm"
include "simpr.mm"
include "xrltnled.mm"
include "mpbird.mm"
include "xrltled.mm"
include "condan.mm"
include "wb.mm"
include "ioo0.mm"
include "eqtr3d.mm"
include "uneq12d.mm"
include "3eqtrrd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cdm.mm"
include "volf.mm"
include "wral.mm"
include "ioombl.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ffnfv.mm"
include "adantlr.mm"
include "simpll.mm"
include "eldif.mm"
include "bicomi.mm"
include "syl6eqelr.mm"
include "pm2.61dan.mm"
include "wfun.mm"
include "fnfun.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvco.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem ovolval4lem1
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume ovolval4lem1.f: |- ( ph -> F : NN --> ( RR* X. RR* ) )
  assume ovolval4lem1.g: |- G = ( n e. NN |-> <. ( 1st ` ( F ` n ) ) , if ( ( 1st ` ( F ` n ) ) <_ ( 2nd ` ( F ` n ) ) , ( 2nd ` ( F ` n ) ) , ( 1st ` ( F ` n ) ) ) >. )
  assume ovolval4lem1.a: |- A = { n e. NN | ( 1st ` ( F ` n ) ) <_ ( 2nd ` ( F ` n ) ) }

  disjoint A n
  disjoint F n
  disjoint G n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( U. ran ( (,) o. F ) = U. ran ( (,) o. G ) /\ ( vol o. ( (,) o. F ) ) = ( vol o. ( (,) o. G ) ) ) )

  proof
    wph
    cioo
    cF
    ccom
    #
    crn
    cuni
    #
    cioo
    cG
    ccom
    #
    crn
    cuni
    #
    wceq
    cvol
    @0
    ccom
    #
    cvol
    @2
    ccom
    #
    wceq
    wph
    @1
    vn
    cn
    vn
    cv
    #
    @0
    cfv
    #
    ciun
    #
    vn
    cA
    @7
    ciun
    #
    vn
    cn
    cA
    cdif
    #
    @7
    ciun
    #
    cun
    #
    @3
    wph
    @8
    @1
    wph
    @0
    cn
    wfn
    #
    @8
    @1
    wceq
    wph
    cn
    cr
    cpw
    #
    @0
    wf
    #
    @13
    wph
    cxr
    cxr
    cxp
    #
    @14
    cioo
    wf
    #
    cn
    @16
    cF
    wf
    #
    @15
    @17
    wph
    ioof
    a1i
    #
    ovolval4lem1.f
    cn
    @16
    @14
    cioo
    cF
    fco
    syl2anc
    cn
    @14
    @0
    ffn
    syl
    #
    vn
    cn
    @0
    fniunfv
    syl
    eqcomd
    @8
    @12
    wceq
    wph
    @8
    vn
    cA
    @10
    cun
    #
    @7
    ciun
    @12
    vn
    cn
    @21
    @7
    @21
    cn
    cA
    cn
    wss
    @21
    cn
    wceq
    cA
    @6
    cF
    cfv
    #
    c1st
    cfv
    #
    @22
    c2nd
    cfv
    #
    cle
    wbr
    #
    vn
    cn
    crab
    #
    cn
    ovolval4lem1.a
    @25
    vn
    cn
    ssrab2
    eqsstri
    #
    cA
    cn
    undif
    mpbi
    eqcomi
    #
    iuneq1i
    vn
    cA
    @10
    @7
    iunxun
    eqtri
    a1i
    wph
    @3
    vn
    cn
    @6
    @2
    cfv
    #
    ciun
    #
    vn
    cA
    @29
    ciun
    #
    vn
    @10
    @29
    ciun
    #
    cun
    #
    @12
    wph
    @30
    @3
    wph
    @2
    cn
    wfn
    #
    @30
    @3
    wceq
    wph
    cn
    @14
    @2
    wf
    #
    @34
    wph
    @17
    cn
    @16
    cG
    wf
    #
    @35
    @19
    wph
    vn
    cn
    @23
    @25
    @24
    @23
    cif
    #
    cop
    #
    @16
    cG
    wph
    @6
    cn
    wcel
    #
    wa
    #
    @23
    @37
    cxr
    cxr
    @40
    @22
    @16
    wcel
    #
    @23
    cxr
    wcel
    #
    wph
    cn
    @16
    @6
    cF
    ovolval4lem1.f
    ffvelrnda
    #
    @22
    cxr
    cxr
    xp1st
    syl
    #
    @40
    @25
    @24
    @23
    cxr
    @40
    @41
    @24
    cxr
    wcel
    #
    @43
    @22
    cxr
    cxr
    xp2nd
    syl
    #
    @44
    ifcld
    opelxpd
    #
    ovolval4lem1.g
    fmptd
    #
    cn
    @16
    @14
    cioo
    cG
    fco
    syl2anc
    cn
    @14
    @2
    ffn
    syl
    #
    vn
    cn
    @2
    fniunfv
    syl
    eqcomd
    @30
    @33
    wceq
    wph
    @30
    vn
    @21
    @29
    ciun
    @33
    vn
    cn
    @21
    @29
    @28
    iuneq1i
    vn
    cA
    @10
    @29
    iunxun
    eqtri
    a1i
    wph
    @31
    @9
    @32
    @11
    wph
    vn
    cA
    @29
    @7
    wph
    @6
    cA
    wcel
    #
    wa
    #
    @29
    @6
    cG
    cfv
    #
    cioo
    cfv
    #
    @7
    @51
    @36
    @39
    @29
    @53
    wceq
    #
    wph
    @36
    @50
    @48
    adantr
    @50
    @39
    wph
    cA
    cn
    @6
    @27
    sseli
    adantl
    #
    cn
    @16
    @6
    cioo
    cG
    fvco3
    #
    syl2anc
    @51
    @7
    @22
    cioo
    cfv
    #
    @53
    @51
    @18
    @39
    @7
    @57
    wceq
    #
    wph
    @18
    @50
    ovolval4lem1.f
    adantr
    @55
    cn
    @16
    @6
    cioo
    cF
    fvco3
    #
    syl2anc
    @51
    @22
    @52
    cioo
    @51
    @22
    @23
    @24
    cop
    #
    @52
    @51
    wph
    @39
    @22
    @60
    wceq
    #
    wph
    @50
    simpl
    #
    @55
    @40
    @41
    @61
    @43
    @22
    cxr
    cxr
    1st2nd2
    syl
    #
    syl2anc
    @51
    @52
    @38
    @60
    @60
    @51
    wph
    @39
    @52
    @38
    wceq
    #
    @62
    @55
    wph
    vn
    cn
    @38
    cG
    cvv
    cG
    vn
    cn
    @38
    cmpt
    wceq
    wph
    ovolval4lem1.g
    a1i
    @40
    @38
    @16
    @47
    elexd
    fvmpt2d
    #
    syl2anc
    @51
    @37
    @24
    @23
    @51
    @25
    @24
    @23
    @50
    @25
    wph
    @50
    @39
    @25
    @50
    @6
    @26
    wcel
    #
    @39
    @25
    wa
    #
    @50
    @66
    cA
    @26
    @6
    ovolval4lem1.a
    eleq2i
    #
    biimpi
    @25
    vn
    cn
    rabid
    #
    sylib
    simprd
    adantl
    iftrued
    opeq2d
    @51
    @60
    eqidd
    3eqtrd
    eqtr4d
    fveq2d
    eqtrd
    eqtr4d
    #
    iuneq2dv
    wph
    @32
    c0
    @11
    wph
    @32
    vn
    @10
    c0
    ciun
    #
    c0
    wph
    vn
    @10
    @29
    c0
    wph
    @6
    @10
    wcel
    #
    wa
    #
    @29
    @53
    @23
    @23
    cop
    #
    cioo
    cfv
    #
    c0
    @73
    @36
    @39
    @54
    wph
    @36
    @72
    @48
    adantr
    @72
    @39
    wph
    @6
    cn
    cA
    eldifi
    #
    adantl
    #
    @56
    syl2anc
    @73
    @52
    @74
    cioo
    @73
    @52
    @38
    @74
    @73
    wph
    @39
    @64
    wph
    @72
    simpl
    #
    @77
    @65
    syl2anc
    @73
    @37
    @23
    @23
    @73
    @25
    @24
    @23
    @73
    @25
    @50
    @72
    @25
    @50
    wph
    @72
    @25
    wa
    #
    @66
    @50
    @79
    @67
    @66
    @72
    @39
    @25
    @76
    anim1i
    @69
    sylibr
    @68
    sylibr
    #
    adantll
    @72
    @50
    wn
    #
    wph
    @25
    @6
    cn
    cA
    eldifn
    #
    ad2antlr
    pm2.65da
    iffalsed
    opeq2d
    eqtrd
    fveq2d
    @75
    c0
    wceq
    @73
    c0
    @23
    @23
    cioo
    co
    #
    @75
    @83
    c0
    @23
    iooid
    eqcomi
    @23
    @23
    cioo
    df-ov
    eqtr2i
    a1i
    3eqtrd
    #
    iuneq2dv
    @71
    c0
    wceq
    wph
    vn
    @10
    iun0
    a1i
    #
    eqtrd
    wph
    @11
    @71
    c0
    wph
    vn
    @10
    @7
    c0
    @73
    @7
    @57
    @60
    cioo
    cfv
    #
    c0
    @73
    @18
    @39
    @58
    @73
    wph
    @18
    @78
    ovolval4lem1.f
    syl
    @77
    @59
    syl2anc
    @73
    @22
    @60
    cioo
    @73
    wph
    @39
    @61
    @78
    @77
    @63
    syl2anc
    fveq2d
    @73
    @23
    @24
    cioo
    co
    #
    @86
    c0
    @87
    @86
    wceq
    @73
    @23
    @24
    cioo
    df-ov
    #
    a1i
    @73
    @87
    c0
    wceq
    #
    @24
    @23
    cle
    wbr
    #
    @73
    @90
    @50
    @73
    @90
    wn
    #
    wa
    #
    @72
    @25
    @50
    wph
    @72
    @91
    simplr
    @92
    @23
    @24
    @73
    @42
    @91
    wph
    @72
    @39
    @42
    @77
    @44
    syldan
    #
    adantr
    #
    @73
    @45
    @91
    wph
    @72
    @39
    @45
    @77
    @46
    syldan
    #
    adantr
    #
    @92
    @23
    @24
    clt
    wbr
    @91
    @73
    @91
    simpr
    @92
    @23
    @24
    @94
    @96
    xrltnled
    mpbird
    xrltled
    @80
    syl2anc
    @72
    @81
    wph
    @91
    @82
    ad2antlr
    condan
    @73
    @42
    @45
    @89
    @90
    wb
    @93
    @95
    @23
    @24
    ioo0
    syl2anc
    mpbird
    #
    eqtr3d
    3eqtrd
    #
    iuneq2dv
    @85
    eqtrd
    eqtr4d
    uneq12d
    3eqtrrd
    3eqtrd
    wph
    vn
    cn
    @4
    @5
    wph
    cn
    cc0
    cpnf
    cicc
    co
    #
    @4
    wf
    #
    @4
    cn
    wfn
    wph
    cvol
    cdm
    #
    @99
    cvol
    wf
    #
    cn
    @101
    @0
    wf
    #
    @100
    @102
    wph
    volf
    a1i
    #
    wph
    @13
    @7
    @101
    wcel
    #
    vn
    cn
    wral
    #
    wa
    @103
    wph
    @13
    @106
    @20
    wph
    @105
    vn
    cn
    @40
    @7
    @87
    @101
    @40
    @7
    @57
    @86
    @87
    @40
    @18
    @39
    @58
    wph
    @18
    @39
    ovolval4lem1.f
    adantr
    wph
    @39
    simpr
    #
    @59
    syl2anc
    @40
    @22
    @60
    cioo
    @63
    fveq2d
    @86
    @87
    wceq
    @40
    @87
    @86
    @88
    eqcomi
    a1i
    3eqtrd
    @87
    @101
    wcel
    @40
    @23
    @24
    ioombl
    #
    a1i
    eqeltrd
    #
    ralrimiva
    jca
    vn
    cn
    @101
    @0
    ffnfv
    sylibr
    #
    cn
    @101
    @99
    cvol
    @0
    fco
    syl2anc
    cn
    @99
    @4
    ffn
    syl
    wph
    cn
    @99
    @5
    wf
    #
    @5
    cn
    wfn
    wph
    @102
    cn
    @101
    @2
    wf
    #
    @111
    @104
    wph
    @34
    @29
    @101
    wcel
    #
    vn
    cn
    wral
    #
    wa
    @112
    wph
    @34
    @114
    @49
    wph
    @113
    vn
    cn
    @40
    @50
    @113
    @40
    @50
    wa
    #
    @29
    @7
    @101
    wph
    @50
    @29
    @7
    wceq
    @39
    @70
    adantlr
    #
    @40
    @105
    @50
    @109
    adantr
    eqeltrd
    @40
    @81
    wa
    #
    wph
    @72
    @113
    wph
    @39
    @81
    simpll
    #
    @39
    @81
    @72
    wph
    @39
    @81
    wa
    #
    @72
    @72
    @119
    @6
    cn
    cA
    eldif
    bicomi
    biimpi
    adantll
    #
    @73
    @29
    c0
    @101
    @84
    @73
    c0
    @87
    @101
    @97
    @108
    syl6eqelr
    eqeltrd
    syl2anc
    pm2.61dan
    ralrimiva
    jca
    vn
    cn
    @101
    @2
    ffnfv
    sylibr
    #
    cn
    @101
    @99
    cvol
    @2
    fco
    syl2anc
    cn
    @99
    @5
    ffn
    syl
    @40
    @7
    cvol
    cfv
    #
    @29
    cvol
    cfv
    #
    @6
    @4
    cfv
    #
    @6
    @5
    cfv
    #
    @40
    @7
    @29
    cvol
    @40
    @50
    @7
    @29
    wceq
    #
    @115
    @29
    @7
    @116
    eqcomd
    @117
    wph
    @72
    @126
    @118
    @120
    @73
    @7
    c0
    @29
    @98
    @84
    eqtr4d
    syl2anc
    pm2.61dan
    fveq2d
    @40
    @0
    wfun
    #
    @6
    @0
    cdm
    #
    wcel
    @124
    @122
    wceq
    wph
    @127
    @39
    wph
    @13
    @127
    @20
    cn
    @0
    fnfun
    syl
    adantr
    @40
    @6
    cn
    @128
    @107
    wph
    cn
    @128
    wceq
    @39
    wph
    @128
    cn
    wph
    @103
    @128
    cn
    wceq
    @110
    cn
    @101
    @0
    fdm
    syl
    eqcomd
    adantr
    eleqtrd
    @6
    cvol
    @0
    fvco
    syl2anc
    @40
    @2
    wfun
    #
    @6
    @2
    cdm
    #
    wcel
    @125
    @123
    wceq
    wph
    @129
    @39
    wph
    @34
    @129
    @49
    cn
    @2
    fnfun
    syl
    adantr
    @40
    @6
    cn
    @130
    @107
    wph
    cn
    @130
    wceq
    @39
    wph
    @130
    cn
    wph
    @112
    @130
    cn
    wceq
    @121
    cn
    @101
    @2
    fdm
    syl
    eqcomd
    adantr
    eleqtrd
    @6
    cvol
    @2
    fvco
    syl2anc
    3eqtr4d
    eqfnfvd
    jca
end
