include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmin.mm"
include "cv.mm"
include "c0p.mm"
include "wceq.mm"
include "cdgr.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cply.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cc.mm"
include "wss.mm"
include "cdiv.mm"
include "cn0.mm"
include "plybss.mm"
include "syl.mm"
include "c1.mm"
include "cc0.mm"
include "wf.mm"
include "plydivlem1.mm"
include "coef2.mm"
include "syl2anc.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "wne.mm"
include "wb.mm"
include "dgreq0.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "divrecd.mm"
include "wi.mm"
include "fvex.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "ex.mm"
include "mp2and.mm"
include "caovcld.mm"
include "eqeltrd.mm"
include "ply1term.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simpr.mm"
include "adantlr.mm"
include "plyadd.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "plyf.mm"
include "mulcl.mm"
include "adantl.mm"
include "inidm.mm"
include "off.mm"
include "w3a.mm"
include "subsub4.mm"
include "caofass.mm"
include "mulcom.mm"
include "caofcom.mm"
include "oveq1d.mm"
include "adddi.mm"
include "caofdi.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "biimpa.mm"
include "syl5eq.mm"
include "rspcev.mm"
include "wral.mm"
include "plymul.mm"
include "plysub.mm"
include "cle.mm"
include "ccoe.mm"
include "cif.mm"
include "eqid.mm"
include "dgrsub.mm"
include "csn.mm"
include "cxp.mm"
include "divne0d.mm"
include "coe1term.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "3netr4d.mm"
include "fveq2.mm"
include "coe0.mm"
include "fveq1d.mm"
include "necon3i.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "dgr1term.mm"
include "nn0cnd.mm"
include "npcand.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "breqtrd.mm"
include "coesub.mm"
include "wfn.mm"
include "coef3.mm"
include "ffn.mm"
include "3syl.mm"
include "nn0ex.mm"
include "eqidd.mm"
include "coemulhi.mm"
include "divcan1d.mm"
include "3eqtr3d.mm"
include "ofval.mm"
include "mpdan.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "nn0red.mm"
include "ltsub1d.mm"
include "breq2d.mm"
include "bitrd.mm"
include "orbi2d.mm"
include "dgrlt.mm"
include "bitr3d.mm"
include "mpbir2and.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl3c.mm"
include "r19.29a.mm"

theorem plydivlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let vd: setvar d
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
  assume plydiv.d: |- ( ph -> D e. NN0 )
  assume plydiv.e: |- ( ph -> ( M - N ) = D )
  assume plydiv.fz: |- ( ph -> F =/= 0p )
  assume plydiv.u: |- U = ( f oF - ( G oF x. p ) )
  assume plydiv.h: |- H = ( z e. CC |-> ( ( ( A ` M ) / ( B ` N ) ) x. ( z ^ D ) ) )
  assume plydiv.al: |- ( ph -> A. f e. ( Poly ` S ) ( ( f = 0p \/ ( ( deg ` f ) - N ) < D ) -> E. p e. ( Poly ` S ) ( U = 0p \/ ( deg ` U ) < N ) ) )
  assume plydiv.a: |- A = ( coeff ` F )
  assume plydiv.b: |- B = ( coeff ` G )
  assume plydiv.m: |- M = ( deg ` F )
  assume plydiv.n: |- N = ( deg ` G )

  disjoint p ph
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
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
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H f
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint ph x
  disjoint ph y
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
  disjoint G f
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R f
  disjoint R p
  disjoint R x
  disjoint R y
  disjoint S f
  disjoint S p
  disjoint S q
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint d ph
  disjoint T x
  disjoint T y
  disjoint d g
  disjoint d w
  disjoint G d
  disjoint f g
  disjoint f w
  disjoint g p
  disjoint g q
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint p w
  disjoint q w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint R d
  disjoint S d
  disjoint S g
  assert |- ( ph -> E. q e. ( Poly ` S ) ( R = 0p \/ ( deg ` R ) < N ) )

  proof
    wph
    cF
    cH
    cG
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
    cG
    vp
    cv
    #
    @0
    co
    #
    @2
    co
    #
    c0p
    wceq
    #
    @6
    cdgr
    cfv
    #
    cN
    clt
    wbr
    #
    wo
    #
    cR
    c0p
    wceq
    #
    cR
    cdgr
    cfv
    #
    cN
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
    vp
    @15
    wph
    @4
    @15
    wcel
    #
    wa
    #
    @10
    wa
    cH
    @4
    caddc
    cof
    #
    co
    #
    @15
    wcel
    #
    cF
    cG
    @20
    @0
    co
    #
    @2
    co
    #
    c0p
    wceq
    #
    @23
    cdgr
    cfv
    #
    cN
    clt
    wbr
    #
    wo
    #
    @16
    @18
    @21
    @10
    @18
    vx
    vy
    cS
    cH
    @4
    wph
    cH
    @15
    wcel
    #
    @17
    wph
    cS
    cc
    wss
    #
    cM
    cA
    cfv
    #
    cN
    cB
    cfv
    #
    cdiv
    co
    #
    cS
    wcel
    cD
    cn0
    wcel
    #
    @28
    wph
    cF
    @15
    wcel
    #
    @29
    plydiv.f
    cS
    cF
    plybss
    syl
    #
    wph
    @32
    @30
    c1
    @31
    cdiv
    co
    #
    cmul
    co
    cS
    wph
    @30
    @31
    wph
    cS
    cc
    @30
    @35
    wph
    cn0
    cS
    cM
    cA
    wph
    @34
    cc0
    cS
    wcel
    #
    cn0
    cS
    cA
    wf
    plydiv.f
    wph
    vx
    vy
    cS
    plydiv.pl
    plydiv.tm
    plydiv.rc
    plydiv.m1
    plydivlem1
    #
    cA
    cS
    cF
    plydiv.a
    coef2
    syl2anc
    wph
    cM
    cF
    cdgr
    cfv
    #
    cn0
    plydiv.m
    wph
    @34
    @39
    cn0
    wcel
    plydiv.f
    cS
    cF
    dgrcl
    syl
    syl5eqel
    #
    ffvelrnd
    #
    sseldd
    #
    wph
    cS
    cc
    @31
    @35
    wph
    cn0
    cS
    cN
    cB
    wph
    cG
    @15
    wcel
    #
    @37
    cn0
    cS
    cB
    wf
    plydiv.g
    @38
    cB
    cS
    cG
    plydiv.b
    coef2
    syl2anc
    wph
    cN
    cG
    cdgr
    cfv
    #
    cn0
    plydiv.n
    wph
    @43
    @44
    cn0
    wcel
    plydiv.g
    cS
    cG
    dgrcl
    syl
    syl5eqel
    #
    ffvelrnd
    #
    sseldd
    #
    wph
    cG
    c0p
    wne
    #
    @31
    cc0
    wne
    #
    plydiv.z
    wph
    cG
    c0p
    @31
    cc0
    wph
    @43
    cG
    c0p
    wceq
    @31
    cc0
    wceq
    wb
    plydiv.g
    cB
    cS
    cG
    cN
    plydiv.n
    plydiv.b
    dgreq0
    syl
    necon3bid
    mpbid
    #
    divrecd
    wph
    vx
    vy
    @30
    @36
    cS
    cS
    cS
    cmul
    plydiv.tm
    @41
    wph
    @31
    cS
    wcel
    #
    @49
    @36
    cS
    wcel
    #
    @46
    @50
    wph
    @51
    @49
    wa
    #
    @52
    wph
    vx
    cv
    #
    cS
    wcel
    #
    @54
    cc0
    wne
    #
    wa
    #
    wa
    #
    c1
    @54
    cdiv
    co
    #
    cS
    wcel
    #
    wi
    wph
    @53
    wa
    #
    @52
    wi
    vx
    @31
    cN
    cB
    fvex
    @54
    @31
    wceq
    #
    @58
    @61
    @60
    @52
    @62
    @57
    @53
    wph
    @62
    @55
    @51
    @56
    @49
    @54
    @31
    cS
    eleq1
    @54
    @31
    cc0
    neeq1
    anbi12d
    anbi2d
    @62
    @59
    @36
    cS
    @54
    @31
    c1
    cdiv
    oveq2
    eleq1d
    imbi12d
    plydiv.rc
    vtocl
    ex
    mp2and
    caovcld
    eqeltrd
    #
    plydiv.d
    vz
    @32
    cS
    cH
    cD
    plydiv.h
    ply1term
    syl3anc
    #
    adantr
    #
    wph
    @17
    simpr
    wph
    @55
    vy
    cv
    #
    cS
    wcel
    wa
    @54
    @66
    caddc
    co
    cS
    wcel
    @17
    plydiv.pl
    adantlr
    plyadd
    adantr
    @18
    @10
    @27
    @18
    @7
    @24
    @9
    @26
    @18
    @6
    @23
    c0p
    @18
    @6
    cF
    @1
    @5
    @19
    co
    #
    @2
    co
    @23
    @18
    vx
    vy
    vz
    cc
    caddc
    cmin
    cc
    cmin
    cF
    @1
    @5
    cmin
    cvv
    cc
    cvv
    wcel
    @18
    cnex
    a1i
    #
    @18
    @34
    cc
    cc
    cF
    wf
    wph
    @34
    @17
    plydiv.f
    adantr
    cS
    cF
    plyf
    syl
    @18
    vx
    vy
    cc
    cc
    cc
    cmul
    cc
    cc
    cc
    cH
    cG
    cvv
    cvv
    @54
    cc
    wcel
    #
    @66
    cc
    wcel
    #
    wa
    #
    @54
    @66
    cmul
    co
    #
    cc
    wcel
    @18
    @54
    @66
    mulcl
    adantl
    #
    @18
    @28
    cc
    cc
    cH
    wf
    @65
    cS
    cH
    plyf
    syl
    #
    @18
    @43
    cc
    cc
    cG
    wf
    wph
    @43
    @17
    plydiv.g
    adantr
    cS
    cG
    plyf
    syl
    #
    @68
    @68
    cc
    inidm
    #
    off
    @18
    vx
    vy
    cc
    cc
    cc
    cmul
    cc
    cc
    cc
    cG
    @4
    cvv
    cvv
    @73
    @75
    @17
    cc
    cc
    @4
    wf
    wph
    cS
    @4
    plyf
    adantl
    #
    @68
    @68
    @76
    off
    @69
    @70
    vz
    cv
    #
    cc
    wcel
    w3a
    #
    @54
    @66
    cmin
    co
    @78
    cmin
    co
    @54
    @66
    @78
    caddc
    co
    #
    cmin
    co
    wceq
    @18
    @54
    @66
    @78
    subsub4
    adantl
    caofass
    @18
    @67
    @22
    cF
    @2
    @18
    @67
    cG
    cH
    @0
    co
    #
    @5
    @19
    co
    @22
    @18
    @1
    @81
    @5
    @19
    @18
    vx
    vy
    cc
    cmul
    cc
    cH
    cG
    cvv
    @68
    @74
    @75
    @71
    @72
    @66
    @54
    cmul
    co
    wceq
    @18
    @54
    @66
    mulcom
    adantl
    caofcom
    oveq1d
    @18
    vx
    vy
    vz
    cc
    caddc
    cc
    cmul
    cG
    cH
    @4
    cc
    caddc
    cvv
    @68
    @75
    @74
    @77
    @79
    @54
    @80
    cmul
    co
    @72
    @54
    @78
    cmul
    co
    caddc
    co
    wceq
    @18
    @54
    @66
    @78
    adddi
    adantl
    caofdi
    eqtr4d
    oveq2d
    eqtrd
    #
    eqeq1d
    @18
    @8
    @25
    cN
    clt
    @18
    @6
    @23
    cdgr
    @82
    fveq2d
    breq1d
    orbi12d
    biimpa
    @14
    @27
    vq
    @20
    @15
    vq
    cv
    #
    @20
    wceq
    #
    @11
    @24
    @13
    @26
    @84
    cR
    @23
    c0p
    @84
    cR
    cF
    cG
    @83
    @0
    co
    #
    @2
    co
    @23
    plydiv.r
    @84
    @85
    @22
    cF
    @2
    @83
    @20
    cG
    @0
    oveq2
    oveq2d
    syl5eq
    #
    eqeq1d
    @84
    @12
    @25
    cN
    clt
    @84
    cR
    @23
    cdgr
    @86
    fveq2d
    breq1d
    orbi12d
    rspcev
    syl2anc
    wph
    @3
    @15
    wcel
    #
    vf
    cv
    #
    c0p
    wceq
    #
    @88
    cdgr
    cfv
    #
    cN
    cmin
    co
    #
    cD
    clt
    wbr
    #
    wo
    #
    cU
    c0p
    wceq
    #
    cU
    cdgr
    cfv
    #
    cN
    clt
    wbr
    #
    wo
    #
    vp
    @15
    wrex
    #
    wi
    #
    vf
    @15
    wral
    @3
    c0p
    wceq
    #
    @3
    cdgr
    cfv
    #
    cN
    cmin
    co
    #
    cD
    clt
    wbr
    #
    wo
    #
    @10
    vp
    @15
    wrex
    #
    wph
    vx
    vy
    cS
    cF
    @1
    plydiv.f
    wph
    vx
    vy
    cS
    cH
    cG
    @64
    plydiv.g
    plydiv.pl
    plydiv.tm
    plymul
    #
    plydiv.pl
    plydiv.tm
    plydiv.m1
    plysub
    #
    plydiv.al
    wph
    @104
    @101
    cM
    cle
    wbr
    #
    cM
    @3
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    wph
    @101
    cM
    @1
    cdgr
    cfv
    #
    cle
    wbr
    #
    @112
    cM
    cif
    #
    cM
    cle
    wph
    @34
    @1
    @15
    wcel
    #
    @101
    @114
    cle
    wbr
    plydiv.f
    @106
    cS
    cF
    @1
    cM
    @112
    plydiv.m
    @112
    eqid
    dgrsub
    syl2anc
    wph
    @114
    @113
    cM
    cM
    cif
    cM
    wph
    @113
    @112
    cM
    cM
    wph
    @112
    cH
    cdgr
    cfv
    #
    cN
    caddc
    co
    #
    cM
    wph
    @28
    cH
    c0p
    wne
    #
    @43
    @48
    @112
    @117
    wceq
    @64
    wph
    cD
    cH
    ccoe
    cfv
    #
    cfv
    #
    cD
    cn0
    cc0
    csn
    cxp
    #
    cfv
    #
    wne
    @118
    wph
    @32
    cc0
    @120
    @122
    wph
    @30
    @31
    @42
    @47
    wph
    cF
    c0p
    wne
    @30
    cc0
    wne
    plydiv.fz
    wph
    cF
    c0p
    @30
    cc0
    wph
    @34
    cF
    c0p
    wceq
    @30
    cc0
    wceq
    wb
    plydiv.f
    cA
    cS
    cF
    cM
    plydiv.m
    plydiv.a
    dgreq0
    syl
    necon3bid
    mpbid
    @50
    divne0d
    #
    wph
    @120
    cD
    cD
    wceq
    #
    @32
    cc0
    cif
    #
    @32
    wph
    @32
    cc
    wcel
    #
    @33
    @33
    @120
    @125
    wceq
    wph
    cS
    cc
    @32
    @35
    @63
    sseldd
    #
    plydiv.d
    plydiv.d
    vz
    @32
    cH
    cD
    cD
    plydiv.h
    coe1term
    syl3anc
    @124
    @32
    cc0
    cD
    eqid
    iftruei
    syl6eq
    #
    wph
    @33
    @122
    cc0
    wceq
    plydiv.d
    cn0
    cc0
    cD
    c0ex
    fvconst2
    syl
    3netr4d
    cH
    c0p
    @120
    @122
    cH
    c0p
    wceq
    #
    cD
    @119
    @121
    @129
    @119
    c0p
    ccoe
    cfv
    @121
    cH
    c0p
    ccoe
    fveq2
    coe0
    syl6eq
    fveq1d
    necon3i
    syl
    plydiv.g
    plydiv.z
    cS
    cH
    cG
    @116
    cN
    @116
    eqid
    #
    plydiv.n
    dgrmul
    syl22anc
    wph
    @117
    cM
    cN
    cmin
    co
    #
    cN
    caddc
    co
    cM
    wph
    @116
    @131
    cN
    caddc
    wph
    @116
    cD
    @131
    wph
    @126
    @32
    cc0
    wne
    @33
    @116
    cD
    wceq
    @127
    @123
    plydiv.d
    vz
    @32
    cH
    cD
    plydiv.h
    dgr1term
    syl3anc
    #
    plydiv.e
    eqtr4d
    oveq1d
    wph
    cM
    cN
    wph
    cM
    @40
    nn0cnd
    wph
    cN
    @45
    nn0cnd
    npcand
    eqtrd
    #
    eqtrd
    ifeq1d
    @113
    cM
    ifid
    syl6eq
    breqtrd
    wph
    @110
    cM
    cA
    @1
    ccoe
    cfv
    #
    @2
    co
    #
    cfv
    #
    @30
    @30
    cmin
    co
    #
    cc0
    wph
    cM
    @109
    @135
    wph
    @34
    @115
    @109
    @135
    wceq
    plydiv.f
    @106
    cA
    @134
    cS
    cF
    @1
    plydiv.a
    @134
    eqid
    #
    coesub
    syl2anc
    fveq1d
    wph
    cM
    cn0
    wcel
    #
    @136
    @137
    wceq
    @40
    wph
    cn0
    cn0
    @30
    @30
    cmin
    cn0
    cA
    @134
    cvv
    cvv
    cM
    wph
    @34
    cn0
    cc
    cA
    wf
    cA
    cn0
    wfn
    plydiv.f
    cA
    cS
    cF
    plydiv.a
    coef3
    cn0
    cc
    cA
    ffn
    3syl
    wph
    @115
    cn0
    cc
    @134
    wf
    @134
    cn0
    wfn
    @106
    @134
    cS
    @1
    @138
    coef3
    cn0
    cc
    @134
    ffn
    3syl
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    @140
    cn0
    inidm
    wph
    @139
    wa
    @30
    eqidd
    wph
    cM
    @134
    cfv
    #
    @30
    wceq
    @139
    wph
    @117
    @134
    cfv
    #
    @116
    @119
    cfv
    #
    @31
    cmul
    co
    #
    @141
    @30
    wph
    @28
    @43
    @142
    @144
    wceq
    @64
    plydiv.g
    @119
    cB
    cS
    cH
    cG
    @116
    cN
    @119
    eqid
    plydiv.b
    @130
    plydiv.n
    coemulhi
    syl2anc
    wph
    @117
    cM
    @134
    @133
    fveq2d
    wph
    @144
    @32
    @31
    cmul
    co
    @30
    wph
    @143
    @32
    @31
    cmul
    wph
    @143
    @120
    @32
    wph
    @116
    cD
    @119
    @132
    fveq2d
    @128
    eqtrd
    oveq1d
    wph
    @30
    @31
    @42
    @47
    @50
    divcan1d
    eqtrd
    3eqtr3d
    adantr
    ofval
    mpdan
    wph
    @30
    @42
    subidd
    3eqtrd
    wph
    @100
    @101
    cM
    clt
    wbr
    #
    wo
    #
    @104
    @108
    @111
    wa
    #
    wph
    @145
    @103
    @100
    wph
    @145
    @102
    @131
    clt
    wbr
    @103
    wph
    @101
    cM
    cN
    wph
    @101
    wph
    @87
    @101
    cn0
    wcel
    @107
    cS
    @3
    dgrcl
    syl
    nn0red
    wph
    cM
    @40
    nn0red
    wph
    cN
    @45
    nn0red
    ltsub1d
    wph
    @131
    cD
    @102
    clt
    plydiv.e
    breq2d
    bitrd
    orbi2d
    wph
    @87
    @139
    @146
    @147
    wb
    @107
    @40
    @109
    cS
    @3
    cM
    @101
    @101
    eqid
    @109
    eqid
    dgrlt
    syl2anc
    bitr3d
    mpbir2and
    @99
    @104
    @105
    wi
    vf
    @3
    @15
    @88
    @3
    wceq
    #
    @93
    @104
    @98
    @105
    @148
    @89
    @100
    @92
    @103
    @88
    @3
    c0p
    eqeq1
    @148
    @91
    @102
    cD
    clt
    @148
    @90
    @101
    cN
    cmin
    @88
    @3
    cdgr
    fveq2
    oveq1d
    breq1d
    orbi12d
    @148
    @97
    @10
    vp
    @15
    @148
    @94
    @7
    @96
    @9
    @148
    cU
    @6
    c0p
    @148
    cU
    @88
    @5
    @2
    co
    @6
    plydiv.u
    @88
    @3
    @5
    @2
    oveq1
    syl5eq
    #
    eqeq1d
    @148
    @95
    @8
    cN
    clt
    @148
    cU
    @6
    cdgr
    @149
    fveq2d
    breq1d
    orbi12d
    rexbidv
    imbi12d
    rspcv
    syl3c
    r19.29a
end
