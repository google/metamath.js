include "cmul.mm"
include "co.mm"
include "climc.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "limccl.mm"
include "sseldi.mm"
include "mulcld.mm"
include "simpr.mm"
include "adantr.mm"
include "mulcn2.mm"
include "syl3anc.mm"
include "w3a.mm"
include "fmptd.mm"
include "cdm.mm"
include "dmmptd.mm"
include "wf.mm"
include "wss.mm"
include "limcrcl.mm"
include "syl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"
include "simp3d.mm"
include "ellimc3.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "adantrr.mm"
include "adantrl.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "cle.mm"
include "cif.mm"
include "ifcl.mm"
include "3ad2ant2.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nf3an.mm"
include "simp11l.mm"
include "simp1rl.mm"
include "3ad2ant1.mm"
include "jca.mm"
include "simp12.mm"
include "simp13l.mm"
include "jca31.mm"
include "simp1r.mm"
include "simp2.mm"
include "simp3l.mm"
include "simplll.mm"
include "simp1lr.mm"
include "simp3r.mm"
include "simp1l.mm"
include "sselda.mm"
include "syl2anc.mm"
include "subcld.mm"
include "abscld.mm"
include "cr.mm"
include "rpre.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "ifcld.mm"
include "simp3.mm"
include "min1.mm"
include "ltletrd.mm"
include "syl211anc.mm"
include "rsp.mm"
include "syl3c.mm"
include "syld3an1.mm"
include "min2.mm"
include "syl3an1.mm"
include "3exp.mm"
include "ralrimi.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "adantlr.mm"
include "3adant3.mm"
include "ad2antrr.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "fvmpt2.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "chvar.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "simpll3.mm"
include "3imp.mm"
include "3adant1l.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "mpbir2and.mm"

theorem mullimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vc: setvar c
  let vd: setvar d
  assume mullimc.f: |- F = ( x e. A |-> B )
  assume mullimc.g: |- G = ( x e. A |-> C )
  assume mullimc.h: |- H = ( x e. A |-> ( B x. C ) )
  assume mullimc.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume mullimc.c: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume mullimc.x: |- ( ph -> X e. ( F limCC D ) )
  assume mullimc.y: |- ( ph -> Y e. ( G limCC D ) )

  disjoint A x
  disjoint D x
  disjoint X x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint A e
  disjoint A f
  disjoint A y
  disjoint A z
  disjoint a b
  disjoint a e
  disjoint a f
  disjoint a y
  disjoint a z
  disjoint b e
  disjoint b f
  disjoint b y
  disjoint b z
  disjoint e f
  disjoint e y
  disjoint e z
  disjoint f y
  disjoint f z
  disjoint y z
  disjoint A w
  disjoint a w
  disjoint b w
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint D a
  disjoint D b
  disjoint D e
  disjoint D f
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint F a
  disjoint F c
  disjoint F d
  disjoint F y
  disjoint F z
  disjoint a c
  disjoint a d
  disjoint c d
  disjoint c y
  disjoint c z
  disjoint d y
  disjoint d z
  disjoint F e
  disjoint F f
  disjoint G b
  disjoint G d
  disjoint G y
  disjoint G z
  disjoint b d
  disjoint G e
  disjoint G f
  disjoint H a
  disjoint H b
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint b c
  disjoint c w
  disjoint d w
  disjoint X e
  disjoint X f
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y w
  disjoint Y y
  disjoint Y z
  disjoint Y e
  disjoint Y f
  disjoint a ph
  disjoint b ph
  disjoint e ph
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint ph w
  assert |- ( ph -> ( X x. Y ) e. ( H limCC D ) )

  proof
    wph
    cX
    cY
    cmul
    co
    #
    cH
    cD
    climc
    co
    wcel
    @0
    cc
    wcel
    vz
    cv
    #
    cD
    wne
    #
    @1
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    cH
    cfv
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    vw
    crp
    wral
    wph
    cX
    cY
    wph
    cF
    cD
    climc
    co
    #
    cc
    cX
    cD
    cF
    limccl
    mullimc.x
    sseldi
    #
    wph
    cG
    cD
    climc
    co
    #
    cc
    cY
    cD
    cG
    limccl
    mullimc.y
    sseldi
    #
    mulcld
    wph
    @15
    vw
    crp
    wph
    @11
    crp
    wcel
    #
    wa
    #
    vc
    cv
    #
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    va
    cv
    #
    clt
    wbr
    #
    vd
    cv
    #
    cY
    cmin
    co
    #
    cabs
    cfv
    #
    vb
    cv
    #
    clt
    wbr
    #
    wa
    #
    @22
    @27
    cmul
    co
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vd
    cc
    wral
    vc
    cc
    wral
    #
    vb
    crp
    wrex
    va
    crp
    wrex
    #
    @15
    @21
    @20
    cX
    cc
    wcel
    #
    cY
    cc
    wcel
    #
    @39
    wph
    @20
    simpr
    wph
    @40
    @20
    @17
    adantr
    wph
    @41
    @20
    @19
    adantr
    va
    vb
    vd
    vc
    @11
    cX
    cY
    mulcn2
    syl3anc
    @21
    @38
    @15
    va
    vb
    crp
    crp
    @21
    @25
    crp
    wcel
    #
    @30
    crp
    wcel
    #
    wa
    #
    @38
    @15
    @21
    @44
    @38
    w3a
    #
    @7
    @1
    cF
    cfv
    #
    cX
    cmin
    co
    #
    cabs
    cfv
    #
    @25
    clt
    wbr
    #
    @1
    cG
    cfv
    #
    cY
    cmin
    co
    #
    cabs
    cfv
    #
    @30
    clt
    wbr
    #
    wa
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    @15
    @21
    @44
    @57
    @38
    wph
    @44
    @57
    @20
    wph
    @44
    wa
    #
    @2
    @4
    ve
    cv
    #
    clt
    wbr
    #
    wa
    #
    @49
    wi
    #
    vz
    cA
    wral
    #
    @2
    @4
    vf
    cv
    #
    clt
    wbr
    #
    wa
    #
    @53
    wi
    #
    vz
    cA
    wral
    #
    wa
    #
    vf
    crp
    wrex
    ve
    crp
    wrex
    #
    @57
    @58
    @63
    ve
    crp
    wrex
    #
    @68
    vf
    crp
    wrex
    #
    @70
    wph
    @42
    @71
    @43
    wph
    @71
    va
    crp
    wph
    @40
    @71
    va
    crp
    wral
    #
    wph
    cX
    @16
    wcel
    #
    @40
    @73
    wa
    mullimc.x
    wph
    va
    ve
    vz
    cA
    cD
    cX
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    mullimc.b
    mullimc.f
    fmptd
    #
    wph
    cA
    cF
    cdm
    #
    cc
    wph
    vx
    cF
    cA
    cB
    cc
    mullimc.f
    mullimc.b
    dmmptd
    wph
    @76
    cc
    cF
    wf
    #
    @76
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    @74
    @77
    @78
    @79
    w3a
    mullimc.x
    cD
    cX
    cF
    limcrcl
    syl
    #
    simp2d
    eqsstr3d
    #
    wph
    @77
    @78
    @79
    @80
    simp3d
    #
    ellimc3
    mpbid
    simprd
    r19.21bi
    adantrr
    wph
    @43
    @72
    @42
    wph
    @72
    vb
    crp
    wph
    @41
    @72
    vb
    crp
    wral
    #
    wph
    cY
    @18
    wcel
    @41
    @83
    wa
    mullimc.y
    wph
    vb
    vf
    vz
    cA
    cD
    cY
    cG
    wph
    vx
    cA
    cC
    cc
    cG
    mullimc.c
    mullimc.g
    fmptd
    #
    @81
    @82
    ellimc3
    mpbid
    simprd
    r19.21bi
    adantrl
    @63
    @68
    ve
    vf
    crp
    crp
    reeanv
    sylanbrc
    @58
    @69
    @57
    ve
    vf
    crp
    crp
    @58
    @59
    crp
    wcel
    #
    @64
    crp
    wcel
    #
    wa
    #
    @69
    @57
    @58
    @87
    @69
    w3a
    #
    @59
    @64
    cle
    wbr
    #
    @59
    @64
    cif
    #
    crp
    wcel
    #
    @2
    @4
    @90
    clt
    wbr
    #
    wa
    #
    @54
    wi
    #
    vz
    cA
    wral
    #
    @57
    @87
    @58
    @91
    @69
    @89
    @59
    @64
    crp
    ifcl
    3ad2ant2
    @88
    @94
    vz
    cA
    @58
    @87
    @69
    vz
    @58
    vz
    nfv
    @87
    vz
    nfv
    @63
    @68
    vz
    @62
    vz
    cA
    nfra1
    @67
    vz
    cA
    nfra1
    nfan
    nf3an
    @88
    @1
    cA
    wcel
    #
    @93
    @54
    @88
    @96
    @93
    w3a
    #
    @49
    @53
    wph
    @42
    wa
    #
    @87
    wa
    #
    @63
    wa
    #
    @96
    @88
    @93
    @49
    @97
    @98
    @87
    @63
    @97
    wph
    @42
    wph
    @44
    @87
    @69
    @96
    @93
    simp11l
    @88
    @96
    @42
    @93
    @42
    @43
    wph
    @87
    @69
    simp1rl
    #
    3ad2ant1
    jca
    @58
    @87
    @69
    @96
    @93
    simp12
    @63
    @68
    @58
    @87
    @96
    @93
    simp13l
    jca31
    @100
    @96
    @93
    w3a
    #
    @63
    @96
    @61
    @49
    @99
    @63
    @96
    @93
    simp1r
    @100
    @96
    @93
    simp2
    #
    @102
    @2
    @60
    @100
    @96
    @2
    @92
    simp3l
    @102
    wph
    @87
    @96
    @92
    @60
    @100
    @96
    wph
    @93
    wph
    @42
    @87
    @63
    simplll
    3ad2ant1
    @98
    @87
    @63
    @96
    @93
    simp1lr
    @103
    @100
    @96
    @2
    @92
    simp3r
    wph
    @87
    wa
    #
    @96
    @92
    w3a
    #
    @4
    @90
    @59
    @105
    @3
    @105
    @1
    cD
    @105
    wph
    @96
    @1
    cc
    wcel
    wph
    @87
    @96
    @92
    simp1l
    #
    @104
    @96
    @92
    simp2
    wph
    cA
    cc
    @1
    @81
    sselda
    syl2anc
    @105
    wph
    @79
    @106
    @82
    syl
    subcld
    abscld
    #
    @105
    @89
    @59
    @64
    cr
    @104
    @96
    @59
    cr
    wcel
    #
    @92
    @85
    @108
    wph
    @86
    @59
    rpre
    ad2antrl
    3ad2ant1
    #
    @104
    @96
    @64
    cr
    wcel
    #
    @92
    @86
    @110
    wph
    @85
    @64
    rpre
    ad2antll
    3ad2ant1
    #
    ifcld
    #
    @109
    @104
    @96
    @92
    simp3
    #
    @105
    @108
    @110
    @90
    @59
    cle
    wbr
    @109
    @111
    @59
    @64
    min1
    syl2anc
    ltletrd
    syl211anc
    jca
    @62
    vz
    cA
    rsp
    syl3c
    syld3an1
    @88
    @99
    @68
    wa
    #
    @96
    @93
    @53
    @88
    @98
    @87
    @68
    @88
    wph
    @42
    wph
    @44
    @87
    @69
    simp1l
    @101
    jca
    @58
    @87
    @69
    simp2
    @58
    @87
    @63
    @68
    simp3r
    jca31
    @114
    @96
    @93
    w3a
    #
    @68
    @96
    @66
    @53
    @99
    @68
    @96
    @93
    simp1r
    @114
    @96
    @93
    simp2
    #
    @115
    @2
    @65
    @114
    @96
    @2
    @92
    simp3l
    @115
    wph
    @87
    @96
    @92
    @65
    @114
    @96
    wph
    @93
    wph
    @42
    @87
    @68
    simplll
    3ad2ant1
    @98
    @87
    @68
    @96
    @93
    simp1lr
    @116
    @114
    @96
    @2
    @92
    simp3r
    @105
    @4
    @90
    @64
    @107
    @112
    @111
    @113
    @105
    @108
    @110
    @90
    @64
    cle
    wbr
    @109
    @111
    @59
    @64
    min2
    syl2anc
    ltletrd
    syl211anc
    jca
    @67
    vz
    cA
    rsp
    syl3c
    syl3an1
    jca
    3exp
    ralrimi
    @56
    @95
    vy
    @90
    crp
    @5
    @90
    wceq
    #
    @55
    @94
    vz
    cA
    @117
    @7
    @93
    @54
    @117
    @6
    @92
    @2
    @5
    @90
    @4
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    3exp
    rexlimdvv
    mpd
    adantlr
    3adant3
    @45
    @56
    @14
    vy
    crp
    @45
    @5
    crp
    wcel
    #
    wa
    #
    @56
    @14
    @119
    @56
    wa
    #
    @13
    vz
    cA
    @119
    @56
    vz
    @119
    vz
    nfv
    @55
    vz
    cA
    nfra1
    nfan
    @120
    @96
    @7
    @12
    @120
    @96
    @7
    w3a
    #
    @10
    @46
    @50
    cmul
    co
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    @121
    wph
    @96
    @10
    @124
    wceq
    @120
    @96
    wph
    @7
    @45
    wph
    @118
    @56
    wph
    @20
    @44
    @38
    simp1l
    ad2antrr
    3ad2ant1
    #
    @120
    @96
    @7
    simp2
    #
    wph
    @96
    wa
    #
    @9
    @123
    cabs
    @127
    @8
    @122
    @0
    cmin
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @128
    cH
    cfv
    #
    @128
    cF
    cfv
    #
    @128
    cG
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    @127
    @8
    @122
    wceq
    #
    wi
    vx
    vz
    @127
    @136
    vx
    @127
    vx
    nfv
    vx
    @8
    @122
    vx
    @1
    cH
    vx
    cH
    vx
    cA
    cB
    cC
    cmul
    co
    #
    cmpt
    mullimc.h
    vx
    cA
    @137
    nfmpt1
    nfcxfr
    vx
    @1
    nfcv
    #
    nffv
    vx
    @46
    @50
    cmul
    vx
    @1
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    mullimc.f
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    @138
    nffv
    vx
    cmul
    nfcv
    vx
    @1
    cG
    vx
    cG
    vx
    cA
    cC
    cmpt
    mullimc.g
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    @138
    nffv
    nfov
    nfeq
    nfim
    @128
    @1
    wceq
    #
    @130
    @127
    @135
    @136
    @139
    @129
    @96
    wph
    @128
    @1
    cA
    eleq1
    anbi2d
    @139
    @131
    @8
    @134
    @122
    @128
    @1
    cH
    fveq2
    @139
    @132
    @46
    @133
    @50
    cmul
    @128
    @1
    cF
    fveq2
    @128
    @1
    cG
    fveq2
    oveq12d
    eqeq12d
    imbi12d
    @130
    @131
    @137
    @134
    @130
    @129
    @137
    cc
    wcel
    @131
    @137
    wceq
    wph
    @129
    simpr
    #
    @130
    cB
    cC
    mullimc.b
    mullimc.c
    mulcld
    #
    vx
    cA
    @137
    cc
    cH
    mullimc.h
    fvmpt2
    syl2anc
    @130
    cB
    @132
    cC
    @133
    cmul
    @130
    @132
    cB
    @130
    @129
    cB
    cc
    wcel
    @132
    cB
    wceq
    @140
    mullimc.b
    vx
    cA
    cB
    cc
    cF
    mullimc.f
    fvmpt2
    syl2anc
    eqcomd
    @130
    @133
    cC
    @130
    @129
    cC
    cc
    wcel
    @133
    cC
    wceq
    @140
    mullimc.c
    vx
    cA
    cC
    cc
    cG
    mullimc.g
    fvmpt2
    syl2anc
    eqcomd
    oveq12d
    eqtrd
    chvar
    oveq1d
    fveq2d
    syl2anc
    @121
    @46
    cc
    wcel
    #
    @50
    cc
    wcel
    #
    wa
    #
    @38
    @54
    @124
    @11
    clt
    wbr
    #
    @121
    wph
    @96
    @144
    @125
    @126
    @127
    @142
    @143
    wph
    cA
    cc
    @1
    cF
    @75
    ffvelrnda
    wph
    cA
    cc
    @1
    cG
    @84
    ffvelrnda
    jca
    syl2anc
    @120
    @96
    @38
    @7
    @21
    @44
    @38
    @118
    @56
    simpll3
    3ad2ant1
    @56
    @96
    @7
    @54
    @119
    @56
    @96
    @7
    @54
    @55
    vz
    cA
    rsp
    3imp
    3adant1l
    @37
    @54
    @145
    wi
    @49
    @31
    wa
    #
    @46
    @27
    cmul
    co
    #
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    vc
    vd
    @46
    @50
    cc
    cc
    @22
    @46
    wceq
    #
    @32
    @146
    @36
    @150
    @151
    @26
    @49
    @31
    @151
    @24
    @48
    @25
    clt
    @151
    @23
    @47
    cabs
    @22
    @46
    cX
    cmin
    oveq1
    fveq2d
    breq1d
    anbi1d
    @151
    @35
    @149
    @11
    clt
    @151
    @34
    @148
    cabs
    @151
    @33
    @147
    @0
    cmin
    @22
    @46
    @27
    cmul
    oveq1
    oveq1d
    fveq2d
    breq1d
    imbi12d
    @27
    @50
    wceq
    #
    @146
    @54
    @150
    @145
    @152
    @31
    @53
    @49
    @152
    @29
    @52
    @30
    clt
    @152
    @28
    @51
    cabs
    @27
    @50
    cY
    cmin
    oveq1
    fveq2d
    breq1d
    anbi2d
    @152
    @149
    @124
    @11
    clt
    @152
    @148
    @123
    cabs
    @152
    @147
    @122
    @0
    cmin
    @27
    @50
    @46
    cmul
    oveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspc2v
    syl3c
    eqbrtrd
    3exp
    ralrimi
    ex
    reximdva
    mpd
    3exp
    rexlimdvv
    mpd
    ralrimiva
    wph
    vw
    vy
    vz
    cA
    cD
    @0
    cH
    wph
    vx
    cA
    @137
    cc
    cH
    @141
    mullimc.h
    fmptd
    @81
    @82
    ellimc3
    mpbir2and
end
