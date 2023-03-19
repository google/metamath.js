include "cdgr.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "c0p.mm"
include "wceq.mm"
include "wo.mm"
include "cply.mm"
include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "resubcld.mm"
include "arch.mm"
include "wa.mm"
include "olc.mm"
include "cmul.mm"
include "cof.mm"
include "wi.mm"
include "wral.mm"
include "adantr.mm"
include "nnnn0.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "breq2.mm"
include "orbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "adantlr.mm"
include "wne.mm"
include "cdiv.mm"
include "cneg.mm"
include "simprl.mm"
include "eqid.mm"
include "simprr.mm"
include "plydivlem3.mm"
include "expr.mm"
include "ralrimiva.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ccoe.mm"
include "cc.mm"
include "cexp.mm"
include "cmpt.mm"
include "simplll.mm"
include "sylan.mm"
include "simplr.mm"
include "simpllr.mm"
include "simprrr.mm"
include "simprrl.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "sylib.mm"
include "plydivlem4.mm"
include "exp32.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "ancld.mm"
include "cle.mm"
include "cz.mm"
include "wb.mm"
include "adantl.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "zsubcld.mm"
include "nn0z.mm"
include "ad2antlr.mm"
include "zleltp1.mm"
include "syl2anc.mm"
include "zred.mm"
include "nn0re.mm"
include "leloed.mm"
include "bitr3d.mm"
include "wn.mm"
include "pm5.63.mm"
include "df-ne.mm"
include "anbi1i.mm"
include "orbi2i.mm"
include "bitr4i.mm"
include "or12.mm"
include "3bitr4i.mm"
include "orass.mm"
include "syl6bb.mm"
include "jaob.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "sylibrd.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"
include "syl6eqr.mm"
include "rspcv.mm"
include "sylc.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem plydivex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vq: setvar q
  let vf: setvar f
  let vp: setvar p
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  let cH: class H
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  let cT: class T
  let vg: setvar g
  let vw: setvar w
  assume plydiv.pl: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plydiv.tm: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plydiv.rc: |- ( ( ph /\ ( x e. S /\ x =/= 0 ) ) -> ( 1 / x ) e. S )
  assume plydiv.m1: |- ( ph -> -u 1 e. S )
  assume plydiv.f: |- ( ph -> F e. ( Poly ` S ) )
  assume plydiv.g: |- ( ph -> G e. ( Poly ` S ) )
  assume plydiv.z: |- ( ph -> G =/= 0p )
  assume plydiv.r: |- R = ( F oF - ( G oF x. q ) )

  disjoint x y
  disjoint q x
  disjoint q y
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint G q
  disjoint G x
  disjoint G y
  disjoint R x
  disjoint R y
  disjoint S q
  disjoint S x
  disjoint S y
  disjoint f p
  disjoint f ph
  disjoint p ph
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint p q
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q z
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint d ph
  disjoint ph z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N f
  disjoint N p
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint G f
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint G p
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R p
  disjoint S d
  disjoint S f
  disjoint S g
  disjoint S p
  disjoint S z
  assert |- ( ph -> E. q e. ( Poly ` S ) ( R = 0p \/ ( deg ` R ) < ( deg ` G ) ) )

  proof
    wph
    cF
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    cmin
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    vd
    cn
    wrex
    #
    cR
    c0p
    wceq
    #
    cR
    cdgr
    cfv
    #
    @1
    clt
    wbr
    #
    wo
    #
    vq
    cS
    cply
    cfv
    #
    wrex
    #
    wph
    @2
    cr
    wcel
    @5
    wph
    @0
    @1
    wph
    @0
    wph
    cF
    @10
    wcel
    #
    @0
    cn0
    wcel
    plydiv.f
    cS
    cF
    dgrcl
    syl
    nn0red
    wph
    @1
    wph
    cG
    @10
    wcel
    #
    @1
    cn0
    wcel
    #
    plydiv.g
    cS
    cG
    dgrcl
    #
    syl
    nn0red
    resubcld
    @2
    vd
    arch
    syl
    wph
    @4
    @11
    vd
    cn
    @4
    cF
    c0p
    wceq
    #
    @4
    wo
    #
    wph
    @3
    cn
    wcel
    #
    wa
    #
    @11
    @4
    @16
    olc
    @19
    @12
    vf
    cv
    #
    c0p
    wceq
    #
    @20
    cdgr
    cfv
    #
    @1
    cmin
    co
    #
    @3
    clt
    wbr
    #
    wo
    #
    @20
    cG
    vq
    cv
    #
    cmul
    cof
    #
    co
    #
    cmin
    cof
    #
    co
    #
    c0p
    wceq
    #
    @30
    cdgr
    cfv
    #
    @1
    clt
    wbr
    #
    wo
    #
    vq
    @10
    wrex
    #
    wi
    #
    vf
    @10
    wral
    #
    @17
    @11
    wi
    #
    wph
    @12
    @18
    plydiv.f
    adantr
    @18
    wph
    @37
    @18
    @3
    cn0
    wcel
    #
    wph
    @37
    wi
    #
    @3
    nnnn0
    wph
    @21
    @23
    vx
    cv
    #
    clt
    wbr
    #
    wo
    #
    @35
    wi
    #
    vf
    @10
    wral
    #
    wi
    wph
    @21
    @23
    cc0
    clt
    wbr
    #
    wo
    #
    @35
    wi
    #
    vf
    @10
    wral
    #
    wi
    @40
    wph
    @21
    @23
    @3
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wo
    #
    @35
    wi
    #
    vf
    @10
    wral
    #
    wi
    @40
    vx
    vd
    @3
    @41
    cc0
    wceq
    #
    @45
    @49
    wph
    @55
    @44
    @48
    vf
    @10
    @55
    @43
    @47
    @35
    @55
    @42
    @46
    @21
    @41
    cc0
    @23
    clt
    breq2
    orbi2d
    imbi1d
    ralbidv
    imbi2d
    vx
    vd
    weq
    #
    @45
    @37
    wph
    @56
    @44
    @36
    vf
    @10
    @56
    @43
    @25
    @35
    @56
    @42
    @24
    @21
    @41
    @3
    @23
    clt
    breq2
    orbi2d
    imbi1d
    ralbidv
    imbi2d
    #
    @41
    @50
    wceq
    #
    @45
    @54
    wph
    @58
    @44
    @53
    vf
    @10
    @58
    @43
    @52
    @35
    @58
    @42
    @51
    @21
    @41
    @50
    @23
    clt
    breq2
    orbi2d
    imbi1d
    ralbidv
    imbi2d
    @57
    wph
    @48
    vf
    @10
    wph
    @20
    @10
    wcel
    #
    @47
    @35
    wph
    @59
    @47
    wa
    #
    wa
    vx
    vy
    @30
    cS
    @20
    cG
    vq
    wph
    @41
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    wa
    #
    @41
    @62
    caddc
    co
    cS
    wcel
    #
    @60
    plydiv.pl
    adantlr
    wph
    @63
    @41
    @62
    cmul
    co
    cS
    wcel
    #
    @60
    plydiv.tm
    adantlr
    wph
    @61
    @41
    cc0
    wne
    wa
    #
    c1
    @41
    cdiv
    co
    cS
    wcel
    #
    @60
    plydiv.rc
    adantlr
    wph
    c1
    cneg
    cS
    wcel
    #
    @60
    plydiv.m1
    adantr
    wph
    @59
    @47
    simprl
    wph
    @13
    @60
    plydiv.g
    adantr
    wph
    cG
    c0p
    wne
    #
    @60
    plydiv.z
    adantr
    @30
    eqid
    #
    wph
    @59
    @47
    simprr
    plydivlem3
    expr
    ralrimiva
    @39
    wph
    @37
    @54
    wph
    @39
    @37
    @54
    wi
    wph
    @39
    wa
    #
    @37
    @37
    @20
    c0p
    wne
    #
    @23
    @3
    wceq
    #
    wa
    #
    @35
    wi
    #
    vf
    @10
    wral
    #
    wa
    #
    @54
    @71
    @37
    @76
    @37
    vg
    cv
    #
    c0p
    wceq
    #
    @78
    cdgr
    cfv
    #
    @1
    cmin
    co
    #
    @3
    clt
    wbr
    #
    wo
    #
    @78
    @28
    @29
    co
    #
    c0p
    wceq
    #
    @84
    cdgr
    cfv
    #
    @1
    clt
    wbr
    #
    wo
    #
    vq
    @10
    wrex
    #
    wi
    #
    vg
    @10
    wral
    #
    @71
    @76
    @36
    @90
    vf
    vg
    @10
    vf
    vg
    weq
    #
    @25
    @83
    @35
    @89
    @92
    @21
    @79
    @24
    @82
    @20
    @78
    c0p
    eqeq1
    @92
    @23
    @81
    @3
    clt
    @92
    @22
    @80
    @1
    cmin
    @20
    @78
    cdgr
    fveq2
    oveq1d
    breq1d
    orbi12d
    @92
    @34
    @88
    vq
    @10
    @92
    @31
    @85
    @33
    @87
    @92
    @30
    @84
    c0p
    @20
    @78
    @28
    @29
    oveq1
    #
    eqeq1d
    @92
    @32
    @86
    @1
    clt
    @92
    @30
    @84
    cdgr
    @93
    fveq2d
    breq1d
    orbi12d
    rexbidv
    imbi12d
    cbvralv
    @71
    @91
    @75
    vf
    @10
    @71
    @59
    wa
    #
    @91
    @74
    @35
    @94
    @91
    @74
    wa
    #
    wa
    #
    vx
    vy
    vz
    @20
    ccoe
    cfv
    #
    cG
    ccoe
    cfv
    #
    @3
    @30
    cS
    @78
    cG
    vp
    cv
    #
    @27
    co
    #
    @29
    co
    #
    vg
    @20
    cG
    vw
    cc
    @22
    @97
    cfv
    @1
    @98
    cfv
    cdiv
    co
    #
    vw
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    @22
    @1
    vq
    vp
    @96
    wph
    @63
    @64
    wph
    @39
    @59
    @95
    simplll
    #
    plydiv.pl
    sylan
    @96
    wph
    @63
    @65
    @106
    plydiv.tm
    sylan
    @96
    wph
    @66
    @67
    @106
    plydiv.rc
    sylan
    @96
    wph
    @68
    @106
    plydiv.m1
    syl
    @71
    @59
    @95
    simplr
    @96
    wph
    @13
    @106
    plydiv.g
    syl
    @96
    wph
    @69
    @106
    plydiv.z
    syl
    @70
    wph
    @39
    @59
    @95
    simpllr
    @94
    @91
    @72
    @73
    simprrr
    @94
    @91
    @72
    @73
    simprrl
    @101
    eqid
    vw
    vz
    cc
    @105
    @102
    vz
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    vw
    vz
    weq
    @104
    @108
    @102
    cmul
    @103
    @107
    @3
    cexp
    oveq1
    oveq2d
    cbvmptv
    @96
    @91
    @83
    @101
    c0p
    wceq
    #
    @101
    cdgr
    cfv
    #
    @1
    clt
    wbr
    #
    wo
    #
    vp
    @10
    wrex
    #
    wi
    #
    vg
    @10
    wral
    @94
    @91
    @74
    simprl
    @90
    @114
    vg
    @10
    @89
    @113
    @83
    @88
    @112
    vq
    vp
    @10
    vq
    vp
    weq
    #
    @85
    @109
    @87
    @111
    @115
    @84
    @101
    c0p
    @115
    @28
    @100
    @78
    @29
    @26
    @99
    cG
    @27
    oveq2
    oveq2d
    #
    eqeq1d
    @115
    @86
    @110
    @1
    clt
    @115
    @84
    @101
    cdgr
    @116
    fveq2d
    breq1d
    orbi12d
    cbvrexv
    imbi2i
    ralbii
    sylib
    @97
    eqid
    @98
    eqid
    @22
    eqid
    @1
    eqid
    plydivlem4
    exp32
    ralrimdva
    syl5bi
    ancld
    @71
    @54
    @36
    @75
    wa
    #
    vf
    @10
    wral
    @77
    @71
    @53
    @117
    vf
    @10
    @94
    @53
    @25
    @74
    wo
    #
    @35
    wi
    @117
    @94
    @52
    @118
    @35
    @94
    @52
    @21
    @24
    @73
    wo
    #
    wo
    #
    @118
    @94
    @51
    @119
    @21
    @94
    @23
    @3
    cle
    wbr
    #
    @51
    @119
    @94
    @23
    cz
    wcel
    @3
    cz
    wcel
    #
    @121
    @51
    wb
    @94
    @22
    @1
    @94
    @22
    @59
    @22
    cn0
    wcel
    @71
    cS
    @20
    dgrcl
    adantl
    nn0zd
    @94
    @1
    @94
    @13
    @14
    wph
    @13
    @39
    @59
    plydiv.g
    ad2antrr
    @15
    syl
    nn0zd
    zsubcld
    #
    @39
    @122
    wph
    @59
    @3
    nn0z
    ad2antlr
    @23
    @3
    zleltp1
    syl2anc
    @94
    @23
    @3
    @94
    @23
    @123
    zred
    @39
    @3
    cr
    wcel
    wph
    @59
    @3
    nn0re
    ad2antlr
    leloed
    bitr3d
    orbi2d
    @120
    @21
    @24
    @74
    wo
    wo
    #
    @118
    @24
    @21
    @73
    wo
    #
    wo
    @24
    @21
    @74
    wo
    #
    wo
    @120
    @124
    @125
    @126
    @24
    @125
    @21
    @21
    wn
    #
    @73
    wa
    #
    wo
    @126
    @21
    @73
    pm5.63
    @74
    @128
    @21
    @72
    @127
    @73
    @20
    c0p
    df-ne
    anbi1i
    orbi2i
    bitr4i
    orbi2i
    @21
    @24
    @73
    or12
    @21
    @24
    @74
    or12
    3bitr4i
    @21
    @24
    @74
    orass
    bitr4i
    syl6bb
    imbi1d
    @25
    @35
    @74
    jaob
    syl6bb
    ralbidva
    @36
    @75
    vf
    @10
    r19.26
    syl6bb
    sylibrd
    expcom
    a2d
    nn0ind
    syl
    impcom
    @36
    @38
    vf
    cF
    @10
    @20
    cF
    wceq
    #
    @25
    @17
    @35
    @11
    @129
    @21
    @16
    @24
    @4
    @20
    cF
    c0p
    eqeq1
    @129
    @23
    @2
    @3
    clt
    @129
    @22
    @0
    @1
    cmin
    @20
    cF
    cdgr
    fveq2
    oveq1d
    breq1d
    orbi12d
    @129
    @34
    @9
    vq
    @10
    @129
    @31
    @6
    @33
    @8
    @129
    @30
    cR
    c0p
    @129
    @30
    cF
    @28
    @29
    co
    cR
    @20
    cF
    @28
    @29
    oveq1
    plydiv.r
    syl6eqr
    #
    eqeq1d
    @129
    @32
    @7
    @1
    clt
    @129
    @30
    cR
    cdgr
    @130
    fveq2d
    breq1d
    orbi12d
    rexbidv
    imbi12d
    rspcv
    sylc
    syl5
    rexlimdva
    mpd
end
