include "cxp.mm"
include "cmul.mm"
include "cres.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "ax-mulf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnsscn.mm"
include "sstri.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fnssres.mm"
include "a1i.mm"
include "wa.mm"
include "ovres.mm"
include "adantl.mm"
include "breq1.mm"
include "elrab2.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "nnmulcld.mm"
include "simprbi.mm"
include "cz.mm"
include "nnzd.mm"
include "adantr.mm"
include "dvdscmul.mm"
include "syl3anc.mm"
include "dvdsmulc.mm"
include "zmulcld.mm"
include "dvdstr.mm"
include "syl2and.mm"
include "mp2and.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "cop.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "simprll.mm"
include "syl.mm"
include "cgcd.mm"
include "c1.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "simprr.mm"
include "sseldi.mm"
include "simprlr.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "gcdcom.mm"
include "ad2antrr.mm"
include "rpdvds.mm"
include "syl32anc.mm"
include "coprmdvds.mm"
include "eqtr3d.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "nnne0d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "mulcanad.mm"
include "opeq12d.mm"
include "expr.mm"
include "fvres.mm"
include "eqeqan12d.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "ralxp.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "2ralbidv.mm"
include "syl5bb.mm"
include "bitri.mm"
include "sylibr.mm"
include "dff13.mm"
include "wrex.mm"
include "cc0.mm"
include "wn.mm"
include "wne.mm"
include "simpr.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "gcddvds.mm"
include "simprd.mm"
include "opelxpi.mm"
include "rpmulgcd2.mm"
include "syl31anc.mm"
include "syl6eq.mm"
include "wb.mm"
include "gcdeq.mm"
include "syl2anr.mm"
include "mpbird.mm"
include "3eqtr2rd.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem dvdsmulf1o
  let wph: wff ph
  let vx: setvar x
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vi: setvar i
  let vz: setvar z
  let cD: class D
  let vu: setvar u
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let cC: class C
  assume dvdsmulf1o.1: |- ( ph -> M e. NN )
  assume dvdsmulf1o.2: |- ( ph -> N e. NN )
  assume dvdsmulf1o.3: |- ( ph -> ( M gcd N ) = 1 )
  assume dvdsmulf1o.x: |- X = { x e. NN | x || M }
  assume dvdsmulf1o.y: |- Y = { x e. NN | x || N }
  assume dvdsmulf1o.z: |- Z = { x e. NN | x || ( M x. N ) }

  disjoint M x
  disjoint N x
  disjoint A k
  disjoint i z
  disjoint D i
  disjoint D z
  disjoint u x
  disjoint M u
  disjoint N u
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint X i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j z
  disjoint X j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k z
  disjoint X k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m z
  disjoint X m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n z
  disjoint X n
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint X u
  disjoint v w
  disjoint v z
  disjoint X v
  disjoint w z
  disjoint X w
  disjoint X z
  disjoint B j
  disjoint C j
  disjoint C k
  disjoint C w
  disjoint C z
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint Z i
  disjoint Z j
  disjoint Z u
  disjoint Z w
  disjoint Z z
  disjoint i x
  disjoint j x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint w x
  disjoint x z
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( x. |` ( X X. Y ) ) : ( X X. Y ) -1-1-onto-> Z )

  proof
    wph
    cX
    cY
    cxp
    #
    cZ
    cmul
    @0
    cres
    #
    wf1
    #
    @0
    cZ
    @1
    wfo
    #
    @0
    cZ
    @1
    wf1o
    wph
    @0
    cZ
    @1
    wf
    #
    vu
    cv
    #
    @1
    cfv
    #
    vv
    cv
    #
    @1
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vv
    @0
    wral
    #
    vu
    @0
    wral
    #
    @2
    wph
    @1
    @0
    wfn
    #
    vi
    cv
    #
    vj
    cv
    #
    @1
    co
    #
    cZ
    wcel
    #
    vj
    cY
    wral
    vi
    cX
    wral
    @4
    @14
    wph
    cmul
    cc
    cc
    cxp
    #
    wfn
    #
    @0
    @19
    wss
    #
    @14
    @19
    cc
    cmul
    wf
    @20
    ax-mulf
    @19
    cc
    cmul
    ffn
    ax-mp
    cX
    cc
    wss
    cY
    cc
    wss
    @21
    cX
    cn
    cc
    cX
    vx
    cv
    #
    cM
    cdvds
    wbr
    #
    vx
    cn
    crab
    cn
    dvdsmulf1o.x
    @23
    vx
    cn
    ssrab2
    eqsstri
    nnsscn
    sstri
    #
    cY
    cn
    cc
    cY
    @22
    cN
    cdvds
    wbr
    #
    vx
    cn
    crab
    cn
    dvdsmulf1o.y
    @25
    vx
    cn
    ssrab2
    eqsstri
    nnsscn
    sstri
    cX
    cc
    cY
    cc
    xpss12
    mp2an
    @19
    @0
    cmul
    fnssres
    mp2an
    a1i
    wph
    @18
    vi
    vj
    cX
    cY
    wph
    @15
    cX
    wcel
    #
    @16
    cY
    wcel
    #
    wa
    #
    wa
    #
    @17
    @15
    @16
    cmul
    co
    #
    cZ
    @28
    @17
    @30
    wceq
    wph
    @15
    @16
    cX
    cY
    cmul
    ovres
    adantl
    @29
    @30
    cn
    wcel
    @30
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    @30
    cZ
    wcel
    @29
    @15
    @16
    @26
    @15
    cn
    wcel
    #
    wph
    @27
    @26
    @33
    @15
    cM
    cdvds
    wbr
    #
    @23
    @34
    vx
    @15
    cn
    cX
    @22
    @15
    cM
    cdvds
    breq1
    dvdsmulf1o.x
    elrab2
    #
    simplbi
    ad2antrl
    #
    @27
    @16
    cn
    wcel
    #
    wph
    @26
    @27
    @37
    @16
    cN
    cdvds
    wbr
    #
    @25
    @38
    vx
    @16
    cn
    cY
    @22
    @16
    cN
    cdvds
    breq1
    dvdsmulf1o.y
    elrab2
    #
    simplbi
    ad2antll
    #
    nnmulcld
    #
    @29
    @38
    @34
    @32
    @27
    @38
    wph
    @26
    @27
    @37
    @38
    @39
    simprbi
    ad2antll
    #
    @26
    @34
    wph
    @27
    @26
    @33
    @34
    @35
    simprbi
    ad2antrl
    #
    @29
    @38
    @30
    @15
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    @34
    @44
    @31
    cdvds
    wbr
    #
    @32
    @29
    @16
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @38
    @45
    wi
    @29
    @16
    @40
    nnzd
    @29
    cN
    wph
    cN
    cn
    wcel
    #
    @28
    dvdsmulf1o.2
    adantr
    nnzd
    #
    @29
    @15
    @36
    nnzd
    #
    @15
    @16
    cN
    dvdscmul
    syl3anc
    @29
    @49
    cM
    cz
    wcel
    #
    @48
    @34
    @46
    wi
    @52
    @29
    cM
    wph
    cM
    cn
    wcel
    #
    @28
    dvdsmulf1o.1
    adantr
    nnzd
    #
    @51
    cN
    @15
    cM
    dvdsmulc
    syl3anc
    @29
    @30
    cz
    wcel
    @44
    cz
    wcel
    @31
    cz
    wcel
    @45
    @46
    wa
    @32
    wi
    @29
    @30
    @41
    nnzd
    @29
    @15
    cN
    @52
    @51
    zmulcld
    @29
    cM
    cN
    @55
    @51
    zmulcld
    @30
    @44
    @31
    dvdstr
    syl3anc
    syl2and
    mp2and
    @22
    @31
    cdvds
    wbr
    #
    @32
    vx
    @30
    cn
    cZ
    @22
    @30
    @31
    cdvds
    breq1
    dvdsmulf1o.z
    elrab2
    sylanbrc
    eqeltrd
    ralrimivva
    vi
    vj
    cX
    cY
    cZ
    @1
    ffnov
    sylanbrc
    #
    wph
    @30
    vm
    cv
    #
    vn
    cv
    #
    cmul
    co
    #
    wceq
    #
    @15
    @16
    cop
    #
    @58
    @59
    cop
    #
    wceq
    #
    wi
    #
    vn
    cY
    wral
    vm
    cX
    wral
    #
    vj
    cY
    wral
    vi
    cX
    wral
    #
    @13
    wph
    @66
    vi
    vj
    cX
    cY
    @29
    @65
    vm
    vn
    cX
    cY
    @29
    @58
    cX
    wcel
    #
    @59
    cY
    wcel
    #
    wa
    #
    @61
    @64
    @29
    @70
    @61
    wa
    #
    wa
    #
    @15
    @58
    @16
    @59
    @72
    @15
    cn0
    wcel
    @58
    cn0
    wcel
    @15
    @58
    cdvds
    wbr
    #
    @58
    @15
    cdvds
    wbr
    #
    @15
    @58
    wceq
    @72
    @15
    @29
    @33
    @71
    @36
    adantr
    #
    nnnn0d
    @72
    @58
    @72
    @68
    @58
    cn
    wcel
    #
    @29
    @68
    @69
    @61
    simprll
    #
    @68
    @76
    @58
    cM
    cdvds
    wbr
    #
    @23
    @78
    vx
    @58
    cn
    cX
    @22
    @58
    cM
    cdvds
    breq1
    dvdsmulf1o.x
    elrab2
    #
    simplbi
    syl
    #
    nnnn0d
    @72
    @15
    @59
    @58
    cmul
    co
    #
    cdvds
    wbr
    #
    @15
    @59
    cgcd
    co
    c1
    wceq
    #
    @73
    @72
    @15
    @30
    @81
    cdvds
    @72
    @49
    @47
    @15
    @30
    cdvds
    wbr
    @72
    @15
    @75
    nnzd
    #
    @72
    @16
    @29
    @37
    @71
    @40
    adantr
    #
    nnzd
    #
    @15
    @16
    dvdsmul1
    syl2anc
    @72
    @30
    @60
    @81
    @29
    @70
    @61
    simprr
    #
    @72
    @58
    @59
    @72
    cX
    cc
    @58
    @24
    @77
    sseldi
    @72
    @59
    @72
    @69
    @59
    cn
    wcel
    #
    @29
    @68
    @69
    @61
    simprlr
    #
    @69
    @88
    @59
    cN
    cdvds
    wbr
    #
    @25
    @90
    vx
    @59
    cn
    cY
    @22
    @59
    cN
    cdvds
    breq1
    dvdsmulf1o.y
    elrab2
    #
    simplbi
    syl
    #
    nncnd
    #
    mulcomd
    eqtrd
    breqtrd
    @72
    @49
    @59
    cz
    wcel
    #
    @48
    @15
    cN
    cgcd
    co
    #
    c1
    wceq
    @90
    @83
    @84
    @72
    @59
    @92
    nnzd
    #
    @29
    @48
    @71
    @51
    adantr
    #
    @72
    @95
    cN
    @15
    cgcd
    co
    #
    c1
    @72
    @49
    @48
    @95
    @98
    wceq
    @84
    @97
    @15
    cN
    gcdcom
    syl2anc
    @72
    @48
    @49
    @53
    cN
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    @34
    @98
    c1
    wceq
    @97
    @84
    @29
    @53
    @71
    @55
    adantr
    #
    wph
    @100
    @28
    @71
    wph
    @99
    cM
    cN
    cgcd
    co
    #
    c1
    wph
    @48
    @53
    @99
    @102
    wceq
    wph
    cN
    dvdsmulf1o.2
    nnzd
    wph
    cM
    dvdsmulf1o.1
    nnzd
    cN
    cM
    gcdcom
    syl2anc
    dvdsmulf1o.3
    eqtrd
    ad2antrr
    #
    @29
    @34
    @71
    @43
    adantr
    cN
    @15
    cM
    rpdvds
    syl32anc
    eqtrd
    @72
    @69
    @90
    @89
    @69
    @88
    @90
    @91
    simprbi
    syl
    @15
    @59
    cN
    rpdvds
    syl32anc
    @72
    @49
    @94
    @58
    cz
    wcel
    #
    @82
    @83
    wa
    @73
    wi
    @84
    @96
    @72
    @58
    @80
    nnzd
    #
    @15
    @59
    @58
    coprmdvds
    syl3anc
    mp2and
    @72
    @58
    @16
    @15
    cmul
    co
    #
    cdvds
    wbr
    #
    @58
    @16
    cgcd
    co
    c1
    wceq
    #
    @74
    @72
    @58
    @60
    @106
    cdvds
    @72
    @104
    @94
    @58
    @60
    cdvds
    wbr
    @105
    @96
    @58
    @59
    dvdsmul1
    syl2anc
    @72
    @30
    @60
    @106
    @87
    @72
    @15
    @16
    @72
    @15
    @75
    nncnd
    #
    @72
    @16
    @85
    nncnd
    #
    mulcomd
    eqtr3d
    breqtrd
    @72
    @104
    @47
    @48
    @58
    cN
    cgcd
    co
    #
    c1
    wceq
    @38
    @108
    @105
    @86
    @97
    @72
    @111
    cN
    @58
    cgcd
    co
    #
    c1
    @72
    @104
    @48
    @111
    @112
    wceq
    @105
    @97
    @58
    cN
    gcdcom
    syl2anc
    @72
    @48
    @104
    @53
    @100
    @78
    @112
    c1
    wceq
    @97
    @105
    @101
    @103
    @72
    @68
    @78
    @77
    @68
    @76
    @78
    @79
    simprbi
    syl
    cN
    @58
    cM
    rpdvds
    syl32anc
    eqtrd
    @29
    @38
    @71
    @42
    adantr
    @58
    @16
    cN
    rpdvds
    syl32anc
    @72
    @104
    @47
    @49
    @107
    @108
    wa
    @74
    wi
    @105
    @86
    @84
    @58
    @16
    @15
    coprmdvds
    syl3anc
    mp2and
    @15
    @58
    dvdseq
    syl22anc
    #
    @72
    @16
    @59
    @15
    @110
    @93
    @109
    @72
    @15
    @75
    nnne0d
    @72
    @30
    @60
    @15
    @59
    cmul
    co
    @87
    @72
    @15
    @58
    @59
    cmul
    @113
    oveq1d
    eqtr4d
    mulcanad
    opeq12d
    expr
    ralrimivva
    ralrimivva
    @13
    @5
    cmul
    cfv
    #
    @7
    cmul
    cfv
    #
    wceq
    #
    @10
    wi
    #
    vv
    @0
    wral
    #
    vu
    @0
    wral
    @67
    @12
    @118
    vu
    @0
    @5
    @0
    wcel
    #
    @11
    @117
    vv
    @0
    @119
    @7
    @0
    wcel
    #
    wa
    @9
    @116
    @10
    @119
    @120
    @6
    @114
    @8
    @115
    @5
    @0
    cmul
    fvres
    @7
    @0
    cmul
    fvres
    eqeqan12d
    imbi1d
    ralbidva
    ralbiia
    @118
    @66
    vu
    vi
    vj
    cX
    cY
    @118
    @114
    @60
    wceq
    #
    @5
    @63
    wceq
    #
    wi
    #
    vn
    cY
    wral
    vm
    cX
    wral
    @5
    @62
    wceq
    #
    @66
    @117
    @123
    vv
    vm
    vn
    cX
    cY
    @7
    @63
    wceq
    #
    @116
    @121
    @10
    @122
    @125
    @115
    @60
    @114
    @125
    @115
    @63
    cmul
    cfv
    @60
    @7
    @63
    cmul
    fveq2
    @58
    @59
    cmul
    df-ov
    syl6eqr
    eqeq2d
    @7
    @63
    @5
    eqeq2
    imbi12d
    ralxp
    @124
    @123
    @65
    vm
    vn
    cX
    cY
    @124
    @121
    @61
    @122
    @64
    @124
    @114
    @30
    @60
    @124
    @114
    @62
    cmul
    cfv
    @30
    @5
    @62
    cmul
    fveq2
    @15
    @16
    cmul
    df-ov
    syl6eqr
    eqeq1d
    @5
    @62
    @63
    eqeq1
    imbi12d
    2ralbidv
    syl5bb
    ralxp
    bitri
    sylibr
    vu
    vv
    @0
    cZ
    @1
    dff13
    sylanbrc
    wph
    @4
    vw
    cv
    #
    @6
    wceq
    #
    vu
    @0
    wrex
    #
    vw
    cZ
    wral
    @3
    @57
    wph
    @128
    vw
    cZ
    wph
    @126
    cZ
    wcel
    #
    wa
    #
    @126
    cM
    cgcd
    co
    #
    @126
    cN
    cgcd
    co
    #
    cop
    #
    @0
    wcel
    #
    @126
    @133
    @1
    cfv
    #
    wceq
    #
    @128
    @130
    @131
    cX
    wcel
    #
    @132
    cY
    wcel
    #
    @134
    @130
    @131
    cn
    wcel
    #
    @131
    cM
    cdvds
    wbr
    #
    @137
    @130
    @126
    cz
    wcel
    #
    @53
    @126
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @139
    @130
    @126
    @129
    @126
    cn
    wcel
    #
    wph
    @129
    @146
    @126
    @31
    cdvds
    wbr
    #
    @56
    @147
    vx
    @126
    cn
    cZ
    @22
    @126
    @31
    cdvds
    breq1
    dvdsmulf1o.z
    elrab2
    #
    simplbi
    #
    adantl
    nnzd
    #
    @130
    cM
    wph
    @54
    @129
    dvdsmulf1o.1
    adantr
    #
    nnzd
    #
    @130
    cM
    cc0
    wne
    @145
    @130
    cM
    @151
    nnne0d
    @144
    cM
    cc0
    @142
    @143
    simpr
    necon3ai
    syl
    @126
    cM
    gcdn0cl
    syl21anc
    @130
    @131
    @126
    cdvds
    wbr
    #
    @140
    @130
    @141
    @53
    @153
    @140
    wa
    @150
    @152
    @126
    cM
    gcddvds
    syl2anc
    simprd
    @23
    @140
    vx
    @131
    cn
    cX
    @22
    @131
    cM
    cdvds
    breq1
    dvdsmulf1o.x
    elrab2
    sylanbrc
    @130
    @132
    cn
    wcel
    #
    @132
    cN
    cdvds
    wbr
    #
    @138
    @130
    @141
    @48
    @142
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @154
    @150
    @130
    cN
    wph
    @50
    @129
    dvdsmulf1o.2
    adantr
    #
    nnzd
    #
    @130
    cN
    cc0
    wne
    @158
    @130
    cN
    @159
    nnne0d
    @157
    cN
    cc0
    @142
    @156
    simpr
    necon3ai
    syl
    @126
    cN
    gcdn0cl
    syl21anc
    @130
    @132
    @126
    cdvds
    wbr
    #
    @155
    @130
    @141
    @48
    @161
    @155
    wa
    @150
    @160
    @126
    cN
    gcddvds
    syl2anc
    simprd
    @25
    @155
    vx
    @132
    cn
    cY
    @22
    @132
    cN
    cdvds
    breq1
    dvdsmulf1o.y
    elrab2
    sylanbrc
    @131
    @132
    cX
    cY
    opelxpi
    syl2anc
    #
    @130
    @135
    @133
    cmul
    cfv
    #
    @126
    @31
    cgcd
    co
    #
    @126
    @130
    @134
    @135
    @163
    wceq
    @162
    @133
    @0
    cmul
    fvres
    syl
    @130
    @164
    @131
    @132
    cmul
    co
    #
    @163
    @130
    @141
    @53
    @48
    @102
    c1
    wceq
    #
    @164
    @165
    wceq
    @150
    @152
    @160
    wph
    @166
    @129
    dvdsmulf1o.3
    adantr
    @126
    cM
    cN
    rpmulgcd2
    syl31anc
    @131
    @132
    cmul
    df-ov
    syl6eq
    @130
    @164
    @126
    wceq
    #
    @147
    @129
    @147
    wph
    @129
    @146
    @147
    @148
    simprbi
    adantl
    @129
    @146
    @31
    cn
    wcel
    @167
    @147
    wb
    wph
    @149
    wph
    cM
    cN
    dvdsmulf1o.1
    dvdsmulf1o.2
    nnmulcld
    @126
    @31
    gcdeq
    syl2anr
    mpbird
    3eqtr2rd
    @127
    @136
    vu
    @133
    @0
    @5
    @133
    wceq
    @6
    @135
    @126
    @5
    @133
    @1
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ralrimiva
    vu
    vw
    @0
    cZ
    @1
    dffo3
    sylanbrc
    @0
    cZ
    @1
    df-f1o
    sylanbrc
end
