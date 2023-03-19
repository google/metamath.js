include "cn.mm"
include "wcel.mm"
include "ccom.mm"
include "cdgr.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cc.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "cmpt.mm"
include "caddc.mm"
include "cof.mm"
include "cply.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "cn0.mm"
include "coef3.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "expcld.mm"
include "mulcld.mm"
include "npcand.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "subcld.mm"
include "eqidd.mm"
include "offval2.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "clt.mm"
include "wbr.mm"
include "plyssc.mm"
include "sseldi.mm"
include "addcl.mm"
include "adantl.mm"
include "mulcl.mm"
include "plyco.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "wss.mm"
include "ssid.mm"
include "eqid.mm"
include "ply1term.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "plysubcl.mm"
include "syl2anc.mm"
include "c0p.mm"
include "c1.mm"
include "nn0p1nn.mm"
include "eqeltrd.mm"
include "nngt0d.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "idd.mm"
include "wo.mm"
include "cle.mm"
include "ccoe.mm"
include "cif.mm"
include "dgrsub.mm"
include "wne.mm"
include "nnne0d.mm"
include "wb.mm"
include "dgreq0.mm"
include "syl5eq.mm"
include "syl6bir.mm"
include "necon3d.mm"
include "mpd.mm"
include "dgr1term.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "breqtrd.mm"
include "coesub.mm"
include "fveq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "nn0ex.mm"
include "inidm.mm"
include "coe1term.mm"
include "iftruei.mm"
include "ofval.mm"
include "mpdan.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "dgrlt.mm"
include "mpbir2and.mm"
include "mpjaod.mm"
include "cr.mm"
include "nn0red.mm"
include "nnre.mm"
include "nngt0.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "id.mm"
include "expcl.mm"
include "syl2anr.mm"
include "oveq12d.mm"
include "wi.mm"
include "wral.mm"
include "nn0leltp1.mm"
include "mpbird.mm"
include "coeq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "eqtr3d.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "1cnd.mm"
include "plypow.mm"
include "dgrmulc.mm"
include "simpr.mm"
include "dgrcolem1.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "dgradd2.mm"
include "0cn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "0dgr.mm"
include "nn0cnd.mm"
include "mul01d.mm"
include "eqtr4d.mm"
include "ad2antrr.mm"
include "syl5eqr.mm"
include "0dgrb.mm"
include "syl6eqr.mm"
include "3eqtr4d.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem dgrcolem2
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  assume dgrco.1: |- M = ( deg ` F )
  assume dgrco.2: |- N = ( deg ` G )
  assume dgrco.3: |- ( ph -> F e. ( Poly ` S ) )
  assume dgrco.4: |- ( ph -> G e. ( Poly ` S ) )
  assume dgrco.5: |- A = ( coeff ` F )
  assume dgrco.6: |- ( ph -> D e. NN0 )
  assume dgrco.7: |- ( ph -> M = ( D + 1 ) )
  assume dgrco.8: |- ( ph -> A. f e. ( Poly ` CC ) ( ( deg ` f ) <_ D -> ( deg ` ( f o. G ) ) = ( ( deg ` f ) x. N ) ) )

  disjoint A f
  disjoint F f
  disjoint M f
  disjoint N f
  disjoint D f
  disjoint G f
  disjoint f ph
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d x
  disjoint N d
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g x
  disjoint N g
  disjoint h x
  disjoint N h
  disjoint N x
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint h w
  disjoint h y
  disjoint h z
  disjoint G h
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint d ph
  disjoint h ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( deg ` ( F o. G ) ) = ( M x. N ) )

  proof
    wph
    cN
    cn
    wcel
    #
    cF
    cG
    ccom
    #
    cdgr
    cfv
    #
    cM
    cN
    cmul
    co
    #
    wceq
    cN
    cc0
    wceq
    #
    wph
    @0
    wa
    #
    @2
    vx
    cc
    vx
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    cM
    cA
    cfv
    #
    @7
    cM
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cmpt
    #
    vx
    cc
    @11
    cmpt
    #
    caddc
    cof
    co
    #
    cdgr
    cfv
    #
    @14
    cdgr
    cfv
    #
    @3
    wph
    @2
    @16
    wceq
    @0
    wph
    @1
    @15
    cdgr
    wph
    vx
    cc
    @12
    @11
    caddc
    co
    #
    cmpt
    vx
    cc
    @8
    cmpt
    @15
    @1
    wph
    vx
    cc
    @18
    @8
    wph
    @6
    cc
    wcel
    #
    wa
    #
    @8
    @11
    wph
    @19
    @7
    cc
    wcel
    @8
    cc
    wcel
    wph
    cc
    cc
    @6
    cG
    wph
    cG
    cS
    cply
    cfv
    #
    wcel
    #
    cc
    cc
    cG
    wf
    #
    dgrco.4
    cS
    cG
    plyf
    syl
    #
    ffvelrnda
    #
    wph
    cc
    cc
    @7
    cF
    wph
    cF
    @21
    wcel
    #
    cc
    cc
    cF
    wf
    dgrco.3
    cS
    cF
    plyf
    syl
    #
    ffvelrnda
    syldan
    #
    @20
    @9
    @10
    wph
    @9
    cc
    wcel
    #
    @19
    wph
    cn0
    cc
    cM
    cA
    wph
    @26
    cn0
    cc
    cA
    wf
    #
    dgrco.3
    cA
    cS
    cF
    dgrco.5
    coef3
    syl
    #
    wph
    cM
    cF
    cdgr
    cfv
    #
    cn0
    dgrco.1
    wph
    @26
    @32
    cn0
    wcel
    dgrco.3
    cS
    cF
    dgrcl
    syl
    syl5eqel
    #
    ffvelrnd
    #
    adantr
    #
    @20
    @7
    cM
    @25
    wph
    cM
    cn0
    wcel
    #
    @19
    @33
    adantr
    expcld
    #
    mulcld
    #
    npcand
    mpteq2dva
    wph
    vx
    cc
    @12
    @11
    caddc
    @13
    @14
    cvv
    cc
    cc
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    #
    @20
    @8
    @11
    @28
    @38
    subcld
    @38
    wph
    @13
    eqidd
    wph
    @14
    eqidd
    #
    offval2
    wph
    vx
    vy
    cc
    cc
    @7
    vy
    cv
    #
    cF
    cfv
    #
    @8
    cG
    cF
    @25
    wph
    vx
    cc
    cc
    cG
    @24
    feqmptd
    #
    wph
    vy
    cc
    cc
    cF
    @27
    feqmptd
    #
    @41
    @7
    cF
    fveq2
    #
    fmptco
    #
    3eqtr4rd
    fveq2d
    adantr
    @5
    @13
    cc
    cply
    cfv
    #
    wcel
    #
    @14
    @47
    wcel
    #
    @13
    cdgr
    cfv
    #
    @17
    clt
    wbr
    @16
    @17
    wceq
    wph
    @48
    @0
    wph
    @1
    @14
    cmin
    cof
    #
    co
    #
    @13
    @47
    wph
    vx
    cc
    @8
    @11
    cmin
    @1
    @14
    cvv
    cc
    cc
    @39
    @28
    @38
    @46
    @40
    offval2
    wph
    @1
    @47
    wcel
    @49
    @52
    @47
    wcel
    wph
    vz
    vw
    cc
    cF
    cG
    wph
    @21
    @47
    cF
    cS
    plyssc
    #
    dgrco.3
    sseldi
    #
    wph
    @21
    @47
    cG
    @53
    dgrco.4
    sseldi
    #
    vz
    cv
    #
    cc
    wcel
    vw
    cv
    #
    cc
    wcel
    wa
    #
    @56
    @57
    caddc
    co
    cc
    wcel
    wph
    @56
    @57
    addcl
    adantl
    #
    @58
    @56
    @57
    cmul
    co
    cc
    wcel
    wph
    @56
    @57
    mulcl
    adantl
    #
    plyco
    wph
    vy
    cc
    @9
    @41
    cM
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cG
    ccom
    @14
    @47
    wph
    vx
    vy
    cc
    cc
    @7
    @62
    @11
    cG
    @63
    @25
    @43
    wph
    @63
    eqidd
    #
    @41
    @7
    wceq
    #
    @61
    @10
    @9
    cmul
    @41
    @7
    cM
    cexp
    oveq1
    #
    oveq2d
    #
    fmptco
    wph
    vz
    vw
    cc
    @63
    cG
    wph
    cc
    cc
    wss
    #
    @29
    @36
    @63
    @47
    wcel
    #
    @68
    wph
    cc
    ssid
    a1i
    #
    @34
    @33
    vy
    @9
    cc
    @63
    cM
    @63
    eqid
    #
    ply1term
    syl3anc
    #
    @55
    @59
    @60
    plyco
    eqeltrrd
    #
    cc
    @1
    @14
    plysubcl
    syl2anc
    eqeltrrd
    adantr
    wph
    @49
    @0
    @73
    adantr
    @5
    cF
    @63
    @51
    co
    #
    cdgr
    cfv
    #
    cN
    cmul
    co
    #
    @3
    @50
    @17
    clt
    @5
    @75
    cM
    clt
    wbr
    #
    @76
    @3
    clt
    wbr
    #
    wph
    @77
    @0
    wph
    @74
    c0p
    wceq
    #
    @77
    @77
    wph
    @77
    @79
    cc0
    cM
    clt
    wbr
    wph
    cM
    wph
    cM
    cD
    c1
    caddc
    co
    #
    cn
    dgrco.7
    wph
    cD
    cn0
    wcel
    #
    @80
    cn
    wcel
    dgrco.6
    cD
    nn0p1nn
    syl
    eqeltrd
    #
    nngt0d
    @79
    @75
    cc0
    cM
    clt
    @79
    @75
    c0p
    cdgr
    cfv
    #
    cc0
    @74
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    breq1d
    syl5ibrcom
    wph
    @77
    idd
    wph
    @79
    @77
    wo
    #
    @75
    cM
    cle
    wbr
    #
    cM
    @74
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    wph
    @75
    cM
    @63
    cdgr
    cfv
    #
    cle
    wbr
    #
    @89
    cM
    cif
    #
    cM
    cle
    wph
    cF
    @47
    wcel
    #
    @69
    @75
    @91
    cle
    wbr
    @54
    @72
    cc
    cF
    @63
    cM
    @89
    dgrco.1
    @89
    eqid
    dgrsub
    syl2anc
    wph
    @91
    @90
    cM
    cM
    cif
    cM
    wph
    @90
    @89
    cM
    cM
    wph
    @29
    @9
    cc0
    wne
    #
    @36
    @89
    cM
    wceq
    @34
    wph
    cM
    cc0
    wne
    @93
    wph
    cM
    @82
    nnne0d
    wph
    @9
    cc0
    cM
    cc0
    wph
    @9
    cc0
    wceq
    #
    cF
    c0p
    wceq
    #
    cM
    cc0
    wceq
    wph
    @26
    @95
    @94
    wb
    dgrco.3
    cA
    cS
    cF
    cM
    dgrco.1
    dgrco.5
    dgreq0
    syl
    @95
    cM
    @32
    cc0
    dgrco.1
    @95
    @32
    @83
    cc0
    cF
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    syl5eq
    syl6bir
    necon3d
    mpd
    #
    @33
    vy
    @9
    @63
    cM
    @71
    dgr1term
    syl3anc
    ifeq1d
    @90
    cM
    ifid
    syl6eq
    breqtrd
    wph
    @87
    cM
    cA
    @63
    ccoe
    cfv
    #
    @51
    co
    #
    cfv
    #
    @9
    @9
    cmin
    co
    #
    cc0
    wph
    cM
    @86
    @98
    wph
    @92
    @69
    @86
    @98
    wceq
    @54
    @72
    cA
    @97
    cc
    cF
    @63
    dgrco.5
    @97
    eqid
    #
    coesub
    syl2anc
    fveq1d
    wph
    @36
    @99
    @100
    wceq
    @33
    wph
    cn0
    cn0
    @9
    @9
    cmin
    cn0
    cA
    @97
    cvv
    cvv
    cM
    wph
    @30
    cA
    cn0
    wfn
    @31
    cn0
    cc
    cA
    ffn
    syl
    wph
    cn0
    cc
    @97
    wf
    #
    @97
    cn0
    wfn
    wph
    @69
    @102
    @72
    @97
    cc
    @63
    @101
    coef3
    syl
    cn0
    cc
    @97
    ffn
    syl
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    @103
    cn0
    inidm
    wph
    @36
    wa
    @9
    eqidd
    wph
    cM
    @97
    cfv
    #
    @9
    wceq
    @36
    wph
    @104
    cM
    cM
    wceq
    #
    @9
    cc0
    cif
    #
    @9
    wph
    @29
    @36
    @36
    @104
    @106
    wceq
    @34
    @33
    @33
    vy
    @9
    @63
    cM
    cM
    @71
    coe1term
    syl3anc
    @105
    @9
    cc0
    cM
    eqid
    iftruei
    syl6eq
    adantr
    ofval
    mpdan
    wph
    @9
    @34
    subidd
    3eqtrd
    wph
    @74
    @47
    wcel
    #
    @36
    @84
    @85
    @88
    wa
    wb
    wph
    @92
    @69
    @107
    @54
    @72
    cc
    cF
    @63
    plysubcl
    syl2anc
    #
    @33
    @86
    cc
    @74
    cM
    @75
    @75
    eqid
    @86
    eqid
    dgrlt
    syl2anc
    mpbir2and
    mpjaod
    #
    adantr
    @5
    @75
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    @77
    @78
    wb
    wph
    @110
    @0
    wph
    @75
    wph
    @107
    @75
    cn0
    wcel
    #
    @108
    cc
    @74
    dgrcl
    syl
    #
    nn0red
    adantr
    wph
    @111
    @0
    wph
    cM
    @33
    nn0red
    adantr
    @0
    @112
    wph
    cN
    nnre
    adantl
    @0
    @113
    wph
    cN
    nngt0
    adantl
    @75
    cM
    cN
    ltmul1
    syl112anc
    mpbid
    wph
    @50
    @76
    wceq
    @0
    wph
    @74
    cG
    ccom
    #
    cdgr
    cfv
    #
    @50
    @76
    wph
    @116
    @13
    cdgr
    wph
    vx
    vy
    cc
    cc
    @7
    @42
    @62
    cmin
    co
    @12
    cG
    @74
    @25
    @43
    wph
    vy
    cc
    @42
    @62
    cmin
    cF
    @63
    cvv
    cc
    cc
    @39
    wph
    cc
    cc
    @41
    cF
    @27
    ffvelrnda
    wph
    @41
    cc
    wcel
    #
    wa
    @9
    @61
    wph
    @29
    @118
    @34
    adantr
    @118
    @118
    @36
    @61
    cc
    wcel
    wph
    @118
    id
    @33
    @41
    cM
    expcl
    syl2anr
    mulcld
    @44
    @64
    offval2
    @65
    @42
    @8
    @62
    @11
    cmin
    @45
    @67
    oveq12d
    fmptco
    fveq2d
    wph
    @107
    vf
    cv
    #
    cdgr
    cfv
    #
    cD
    cle
    wbr
    #
    @119
    cG
    ccom
    #
    cdgr
    cfv
    #
    @120
    cN
    cmul
    co
    #
    wceq
    #
    wi
    #
    vf
    @47
    wral
    @75
    cD
    cle
    wbr
    #
    @117
    @76
    wceq
    #
    @108
    dgrco.8
    wph
    @127
    @75
    @80
    clt
    wbr
    #
    wph
    @75
    cM
    @80
    clt
    @109
    dgrco.7
    breqtrd
    wph
    @114
    @81
    @127
    @129
    wb
    @115
    dgrco.6
    @75
    cD
    nn0leltp1
    syl2anc
    mpbird
    @126
    @127
    @128
    wi
    vf
    @74
    @47
    @119
    @74
    wceq
    #
    @121
    @127
    @125
    @128
    @130
    @120
    @75
    cD
    cle
    @119
    @74
    cdgr
    fveq2
    #
    breq1d
    @130
    @123
    @117
    @124
    @76
    @130
    @122
    @116
    cdgr
    @119
    @74
    cG
    coeq1
    fveq2d
    @130
    @120
    @75
    cN
    cmul
    @131
    oveq1d
    eqeq12d
    imbi12d
    rspcv
    syl3c
    eqtr3d
    adantr
    @5
    @17
    vx
    cc
    @10
    cmpt
    #
    cdgr
    cfv
    #
    @3
    wph
    @17
    @133
    wceq
    @0
    wph
    cc
    @9
    csn
    cxp
    #
    @132
    cmul
    cof
    co
    #
    cdgr
    cfv
    #
    @17
    @133
    wph
    @135
    @14
    cdgr
    wph
    vx
    cc
    @9
    @10
    cmul
    @134
    @132
    cvv
    cc
    cc
    @39
    @35
    @37
    @134
    vx
    cc
    @9
    cmpt
    wceq
    wph
    vx
    cc
    @9
    fconstmpt
    a1i
    wph
    @132
    eqidd
    offval2
    fveq2d
    wph
    @29
    @93
    @132
    @47
    wcel
    @136
    @133
    wceq
    @34
    @96
    wph
    vy
    cc
    @61
    cmpt
    #
    cG
    ccom
    @132
    @47
    wph
    vx
    vy
    cc
    cc
    @7
    @61
    @10
    cG
    @137
    @25
    @43
    wph
    @137
    eqidd
    @66
    fmptco
    wph
    vz
    vw
    cc
    @137
    cG
    wph
    @68
    c1
    cc
    wcel
    @36
    @137
    @47
    wcel
    @70
    wph
    1cnd
    @33
    vy
    cc
    cM
    plypow
    syl3anc
    @55
    @59
    @60
    plyco
    eqeltrrd
    @9
    cc
    @132
    dgrmulc
    syl3anc
    eqtr3d
    adantr
    @5
    vx
    cS
    cG
    cM
    cN
    dgrco.2
    wph
    cM
    cn
    wcel
    @0
    @82
    adantr
    wph
    @0
    simpr
    wph
    @22
    @0
    dgrco.4
    adantr
    dgrcolem1
    eqtrd
    #
    3brtr4d
    cc
    @13
    @14
    @50
    @17
    @50
    eqid
    @17
    eqid
    dgradd2
    syl3anc
    @138
    3eqtrd
    wph
    @4
    wa
    #
    cc
    cc0
    cG
    cfv
    #
    cF
    cfv
    #
    csn
    cxp
    #
    cdgr
    cfv
    #
    cM
    cc0
    cmul
    co
    #
    @2
    @3
    wph
    @143
    @144
    wceq
    @4
    wph
    @143
    cc0
    @144
    wph
    @141
    cc
    wcel
    @143
    cc0
    wceq
    wph
    cc
    cc
    @140
    cF
    @27
    wph
    @23
    cc0
    cc
    wcel
    @140
    cc
    wcel
    #
    @24
    0cn
    cc
    cc
    cc0
    cG
    ffvelrn
    sylancl
    #
    ffvelrnd
    @141
    0dgr
    syl
    wph
    cM
    wph
    cM
    @33
    nn0cnd
    mul01d
    eqtr4d
    adantr
    @139
    @1
    @142
    cdgr
    @139
    @1
    vx
    cc
    @141
    cmpt
    @142
    @139
    vx
    vy
    cc
    cc
    @140
    @42
    @141
    cG
    cF
    wph
    @145
    @4
    @19
    @146
    ad2antrr
    @139
    cG
    cc
    @140
    csn
    cxp
    #
    vx
    cc
    @140
    cmpt
    @139
    cG
    cdgr
    cfv
    #
    cc0
    wceq
    #
    cG
    @147
    wceq
    #
    @139
    @148
    cN
    cc0
    dgrco.2
    wph
    @4
    simpr
    #
    syl5eqr
    wph
    @149
    @150
    wb
    #
    @4
    wph
    @22
    @152
    dgrco.4
    cS
    cG
    0dgrb
    syl
    adantr
    mpbid
    vx
    cc
    @140
    fconstmpt
    syl6eq
    wph
    cF
    vy
    cc
    @42
    cmpt
    wceq
    @4
    @44
    adantr
    @41
    @140
    cF
    fveq2
    fmptco
    vx
    cc
    @141
    fconstmpt
    syl6eqr
    fveq2d
    @139
    cN
    cc0
    cM
    cmul
    @151
    oveq2d
    3eqtr4d
    wph
    cN
    cn0
    wcel
    @0
    @4
    wo
    wph
    cN
    @148
    cn0
    dgrco.2
    wph
    @22
    @148
    cn0
    wcel
    dgrco.4
    cS
    cG
    dgrcl
    syl
    syl5eqel
    cN
    elnn0
    sylib
    mpjaodan
end
