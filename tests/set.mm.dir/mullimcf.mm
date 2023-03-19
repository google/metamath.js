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
include "cdm.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "wss.mm"
include "limcrcl.mm"
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
include "a1i.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "fvmptd.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "simpll3.mm"
include "3imp.mm"
include "3adant1l.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "ralrimiva.mm"
include "fmptd.mm"
include "mpbir2and.mm"

theorem mullimcf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vc: setvar c
  let vd: setvar d
  assume mullimcf.f: |- ( ph -> F : A --> CC )
  assume mullimcf.g: |- ( ph -> G : A --> CC )
  assume mullimcf.h: |- H = ( x e. A |-> ( ( F ` x ) x. ( G ` x ) ) )
  assume mullimcf.b: |- ( ph -> B e. ( F limCC D ) )
  assume mullimcf.c: |- ( ph -> C e. ( G limCC D ) )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint F x
  disjoint G x
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
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint B e
  disjoint B f
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint C e
  disjoint C f
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
  disjoint F e
  disjoint F f
  disjoint G b
  disjoint G d
  disjoint G y
  disjoint G z
  disjoint G e
  disjoint G f
  disjoint H a
  disjoint H b
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint a ph
  disjoint b ph
  disjoint e ph
  disjoint f ph
  disjoint ph y
  disjoint ph z
  disjoint ph w
  assert |- ( ph -> ( B x. C ) e. ( H limCC D ) )

  proof
    wph
    cB
    cC
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
    cB
    cC
    wph
    cF
    cD
    climc
    co
    #
    cc
    cB
    cD
    cF
    limccl
    mullimcf.b
    sseldi
    #
    wph
    cG
    cD
    climc
    co
    #
    cc
    cC
    cD
    cG
    limccl
    mullimcf.c
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
    cB
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
    cC
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
    cB
    cc
    wcel
    #
    cC
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
    cB
    cC
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
    cB
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
    cC
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
    cB
    @16
    wcel
    #
    @40
    @73
    wa
    mullimcf.b
    wph
    va
    ve
    vz
    cA
    cD
    cB
    cF
    mullimcf.f
    wph
    cA
    cF
    cdm
    #
    cc
    wph
    cA
    cc
    cF
    wf
    @75
    cA
    wceq
    mullimcf.f
    cA
    cc
    cF
    fdm
    syl
    wph
    @75
    cc
    cF
    wf
    #
    @75
    cc
    wss
    #
    cD
    cc
    wcel
    #
    wph
    @74
    @76
    @77
    @78
    w3a
    mullimcf.b
    cD
    cB
    cF
    limcrcl
    syl
    #
    simp2d
    eqsstr3d
    #
    wph
    @76
    @77
    @78
    @79
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
    cC
    @18
    wcel
    @41
    @82
    wa
    mullimcf.c
    wph
    vb
    vf
    vz
    cA
    cD
    cC
    cG
    mullimcf.g
    @80
    @81
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
    @85
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
    @88
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
    @85
    @58
    @89
    @69
    @87
    @59
    @64
    crp
    ifcl
    3ad2ant2
    @86
    @92
    vz
    cA
    @58
    @85
    @69
    vz
    @58
    vz
    nfv
    @85
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
    @86
    @1
    cA
    wcel
    #
    @91
    @54
    @86
    @94
    @91
    w3a
    #
    @49
    @53
    wph
    @42
    wa
    #
    @85
    wa
    #
    @63
    wa
    #
    @94
    @86
    @91
    @49
    @95
    @96
    @85
    @63
    @95
    wph
    @42
    wph
    @44
    @85
    @69
    @94
    @91
    simp11l
    @86
    @94
    @42
    @91
    @42
    @43
    wph
    @85
    @69
    simp1rl
    #
    3ad2ant1
    jca
    @58
    @85
    @69
    @94
    @91
    simp12
    @63
    @68
    @58
    @85
    @94
    @91
    simp13l
    jca31
    @98
    @94
    @91
    w3a
    #
    @63
    @94
    @61
    @49
    @97
    @63
    @94
    @91
    simp1r
    @98
    @94
    @91
    simp2
    #
    @100
    @2
    @60
    @98
    @94
    @2
    @90
    simp3l
    @100
    wph
    @85
    @94
    @90
    @60
    @98
    @94
    wph
    @91
    wph
    @42
    @85
    @63
    simplll
    3ad2ant1
    @96
    @85
    @63
    @94
    @91
    simp1lr
    @101
    @98
    @94
    @2
    @90
    simp3r
    wph
    @85
    wa
    #
    @94
    @90
    w3a
    #
    @4
    @88
    @59
    @103
    @3
    @103
    @1
    cD
    @103
    wph
    @94
    @1
    cc
    wcel
    wph
    @85
    @94
    @90
    simp1l
    #
    @102
    @94
    @90
    simp2
    wph
    cA
    cc
    @1
    @80
    sselda
    syl2anc
    @103
    wph
    @78
    @104
    @81
    syl
    subcld
    abscld
    #
    @103
    @87
    @59
    @64
    cr
    @102
    @94
    @59
    cr
    wcel
    #
    @90
    @83
    @106
    wph
    @84
    @59
    rpre
    ad2antrl
    3ad2ant1
    #
    @102
    @94
    @64
    cr
    wcel
    #
    @90
    @84
    @108
    wph
    @83
    @64
    rpre
    ad2antll
    3ad2ant1
    #
    ifcld
    #
    @107
    @102
    @94
    @90
    simp3
    #
    @103
    @106
    @108
    @88
    @59
    cle
    wbr
    @107
    @109
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
    @86
    @97
    @68
    wa
    #
    @94
    @91
    @53
    @86
    @96
    @85
    @68
    @86
    wph
    @42
    wph
    @44
    @85
    @69
    simp1l
    @99
    jca
    @58
    @85
    @69
    simp2
    @58
    @85
    @63
    @68
    simp3r
    jca31
    @112
    @94
    @91
    w3a
    #
    @68
    @94
    @66
    @53
    @97
    @68
    @94
    @91
    simp1r
    @112
    @94
    @91
    simp2
    #
    @113
    @2
    @65
    @112
    @94
    @2
    @90
    simp3l
    @113
    wph
    @85
    @94
    @90
    @65
    @112
    @94
    wph
    @91
    wph
    @42
    @85
    @68
    simplll
    3ad2ant1
    @96
    @85
    @68
    @94
    @91
    simp1lr
    @114
    @112
    @94
    @2
    @90
    simp3r
    @103
    @4
    @88
    @64
    @105
    @110
    @109
    @111
    @103
    @106
    @108
    @88
    @64
    cle
    wbr
    @107
    @109
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
    @93
    vy
    @88
    crp
    @5
    @88
    wceq
    #
    @55
    @92
    vz
    cA
    @115
    @7
    @91
    @54
    @115
    @6
    @90
    @2
    @5
    @88
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
    @117
    @56
    wa
    #
    @13
    vz
    cA
    @117
    @56
    vz
    @117
    vz
    nfv
    @55
    vz
    cA
    nfra1
    nfan
    @118
    @94
    @7
    @12
    @118
    @94
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
    @119
    wph
    @94
    @10
    @122
    wceq
    @118
    @94
    wph
    @7
    @45
    wph
    @116
    @56
    wph
    @20
    @44
    @38
    simp1l
    ad2antrr
    3ad2ant1
    #
    @118
    @94
    @7
    simp2
    #
    wph
    @94
    wa
    #
    @9
    @121
    cabs
    @125
    @8
    @120
    @0
    cmin
    @125
    vx
    @1
    vx
    cv
    #
    cF
    cfv
    #
    @126
    cG
    cfv
    #
    cmul
    co
    #
    @120
    cA
    cH
    cc
    cH
    vx
    cA
    @129
    cmpt
    wceq
    @125
    mullimcf.h
    a1i
    @126
    @1
    wceq
    #
    @129
    @120
    wceq
    @125
    @130
    @127
    @46
    @128
    @50
    cmul
    @126
    @1
    cF
    fveq2
    @126
    @1
    cG
    fveq2
    oveq12d
    adantl
    wph
    @94
    simpr
    @125
    @46
    @50
    wph
    cA
    cc
    @1
    cF
    mullimcf.f
    ffvelrnda
    #
    wph
    cA
    cc
    @1
    cG
    mullimcf.g
    ffvelrnda
    #
    mulcld
    fvmptd
    oveq1d
    fveq2d
    syl2anc
    @119
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
    @122
    @11
    clt
    wbr
    #
    @119
    wph
    @94
    @135
    @123
    @124
    @125
    @133
    @134
    @131
    @132
    jca
    syl2anc
    @118
    @94
    @38
    @7
    @21
    @44
    @38
    @116
    @56
    simpll3
    3ad2ant1
    @56
    @94
    @7
    @54
    @117
    @56
    @94
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
    @136
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
    @137
    @36
    @141
    @142
    @26
    @49
    @31
    @142
    @24
    @48
    @25
    clt
    @142
    @23
    @47
    cabs
    @22
    @46
    cB
    cmin
    oveq1
    fveq2d
    breq1d
    anbi1d
    @142
    @35
    @140
    @11
    clt
    @142
    @34
    @139
    cabs
    @142
    @33
    @138
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
    @137
    @54
    @141
    @136
    @143
    @31
    @53
    @49
    @143
    @29
    @52
    @30
    clt
    @143
    @28
    @51
    cabs
    @27
    @50
    cC
    cmin
    oveq1
    fveq2d
    breq1d
    anbi2d
    @143
    @140
    @122
    @11
    clt
    @143
    @139
    @121
    cabs
    @143
    @138
    @120
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
    @129
    cc
    cH
    wph
    @126
    cA
    wcel
    wa
    @127
    @128
    wph
    cA
    cc
    @126
    cF
    mullimcf.f
    ffvelrnda
    wph
    cA
    cc
    @126
    cG
    mullimcf.g
    ffvelrnda
    mulcld
    mullimcf.h
    fmptd
    @80
    @81
    ellimc3
    mpbir2and
end
