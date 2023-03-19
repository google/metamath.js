include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "wcel.mm"
include "cc.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "c2.mm"
include "simpr.mm"
include "rphalfcld.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "caddc.mm"
include "cle.mm"
include "cif.mm"
include "crab.mm"
include "rabid.mm"
include "cin.mm"
include "eliooord.mm"
include "adantl.mm"
include "simprd.mm"
include "biantrurd.mm"
include "ioossre.mm"
include "sseldi.mm"
include "ad3antrrr.mm"
include "rpred.mm"
include "adantr.mm"
include "ltsubaddd.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "ad2antrr.mm"
include "readdcld.mm"
include "xrltmin.mm"
include "syl3anc.mm"
include "3bitr4rd.mm"
include "ifcld.mm"
include "simpld.mm"
include "w3a.mm"
include "elioo5.mm"
include "baibd.mm"
include "syl31anc.mm"
include "ltled.mm"
include "abssubge0d.mm"
include "breq1d.mm"
include "3bitr4d.mm"
include "rabbi2dva.mm"
include "wss.mm"
include "xrmin1.mm"
include "syl2anc.mm"
include "iooss2.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "lbioo.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "bicomd.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "ralbiia.mm"
include "oveq1.mm"
include "ralrab.mm"
include "bitr4i.mm"
include "adantrr.mm"
include "raleqdv.mm"
include "cmul.mm"
include "wf.mm"
include "cdm.mm"
include "cc0.mm"
include "crn.mm"
include "wn.mm"
include "cioc.mm"
include "simprll.mm"
include "iocssre.mm"
include "ifclda.mm"
include "ltaddrp2d.mm"
include "mpbir2and.mm"
include "xrmin2.mm"
include "elioc1.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "simprlr.mm"
include "simprr.mm"
include "lhop1lem.mm"
include "rpcnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "breqtrd.mm"
include "expr.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "sylibrd.mm"
include "adantld.mm"
include "com23.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "syld.mm"
include "anim2d.mm"
include "dvf.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffvelrnda.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "divcld.mm"
include "fmptd.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "recnd.mm"
include "ellimc3.mm"
include "3imtr4d.mm"

theorem lhop1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let vd: setvar d
  let ve: setvar e
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let cR: class R
  let cE: class E
  let cX: class X
  assume lhop1.a: |- ( ph -> A e. RR )
  assume lhop1.b: |- ( ph -> B e. RR* )
  assume lhop1.l: |- ( ph -> A < B )
  assume lhop1.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume lhop1.g: |- ( ph -> G : ( A (,) B ) --> RR )
  assume lhop1.if: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume lhop1.ig: |- ( ph -> dom ( RR _D G ) = ( A (,) B ) )
  assume lhop1.f0: |- ( ph -> 0 e. ( F limCC A ) )
  assume lhop1.g0: |- ( ph -> 0 e. ( G limCC A ) )
  assume lhop1.gn0: |- ( ph -> -. 0 e. ran G )
  assume lhop1.gd0: |- ( ph -> -. 0 e. ran ( RR _D G ) )
  assume lhop1.c: |- ( ph -> C e. ( ( z e. ( A (,) B ) |-> ( ( ( RR _D F ) ` z ) / ( ( RR _D G ) ` z ) ) ) limCC A ) )

  disjoint B z
  disjoint ph z
  disjoint A z
  disjoint C z
  disjoint F z
  disjoint G z
  disjoint d e
  disjoint d r
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B d
  disjoint e r
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint D t
  disjoint d u
  disjoint d w
  disjoint d ph
  disjoint e u
  disjoint e w
  disjoint e ph
  disjoint r u
  disjoint r w
  disjoint ph r
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint R u
  disjoint R w
  disjoint R z
  disjoint d t
  disjoint A d
  disjoint e t
  disjoint A e
  disjoint r t
  disjoint A r
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint E r
  disjoint E t
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint X r
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint C d
  disjoint C e
  disjoint C r
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint F d
  disjoint F e
  disjoint F r
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint G d
  disjoint G e
  disjoint G r
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  assert |- ( ph -> C e. ( ( z e. ( A (,) B ) |-> ( ( F ` z ) / ( G ` z ) ) ) limCC A ) )

  proof
    wph
    cC
    vz
    cA
    cB
    cioo
    co
    #
    vz
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    @1
    cr
    cG
    cdv
    co
    #
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cA
    climc
    co
    wcel
    #
    cC
    vz
    @0
    @1
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cA
    climc
    co
    wcel
    #
    lhop1.c
    wph
    cC
    cc
    wcel
    #
    vy
    cv
    #
    cA
    wne
    #
    @15
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    wa
    #
    @15
    @7
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    @0
    wral
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    #
    wa
    @14
    vv
    cv
    #
    cA
    wne
    #
    @30
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @19
    clt
    wbr
    #
    wa
    #
    @30
    @12
    cfv
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    @0
    wral
    #
    vd
    crp
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @8
    @13
    wph
    @29
    @44
    @14
    wph
    @29
    @43
    vx
    crp
    wph
    @39
    crp
    wcel
    #
    wa
    #
    @29
    @21
    @24
    @39
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wi
    #
    vy
    @0
    wral
    #
    vd
    crp
    wrex
    #
    @43
    @46
    @47
    crp
    wcel
    #
    @29
    @51
    wi
    @46
    @39
    wph
    @45
    simpr
    #
    rphalfcld
    #
    @28
    @51
    ve
    @47
    crp
    @25
    @47
    wceq
    #
    @27
    @49
    vd
    vy
    crp
    @0
    @55
    @26
    @48
    @21
    @25
    @47
    @24
    clt
    breq2
    imbi2d
    rexralbidv
    rspcv
    syl
    @46
    @50
    @42
    vd
    crp
    @46
    @19
    crp
    wcel
    #
    wa
    #
    @50
    @41
    vv
    @0
    @57
    @30
    @0
    wcel
    #
    wa
    #
    @35
    @50
    @40
    @59
    @34
    @50
    @40
    wi
    #
    @31
    @59
    @34
    @50
    @30
    cF
    cfv
    #
    @30
    cG
    cfv
    #
    cdiv
    co
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @39
    clt
    wbr
    #
    wi
    #
    @60
    @57
    @58
    @34
    @67
    @57
    @58
    @34
    wa
    #
    @30
    cA
    cB
    @19
    cA
    caddc
    co
    #
    cle
    wbr
    #
    cB
    @69
    cif
    #
    cioo
    co
    #
    wcel
    #
    @67
    @68
    @30
    @34
    vv
    @0
    crab
    #
    wcel
    @57
    @73
    @34
    vv
    @0
    rabid
    @57
    @74
    @72
    @30
    @57
    @0
    @72
    cin
    #
    @74
    @72
    @57
    @34
    vv
    @0
    @72
    @59
    @30
    @71
    clt
    wbr
    #
    @32
    @19
    clt
    wbr
    #
    @73
    @34
    @59
    @30
    @69
    clt
    wbr
    #
    @30
    cB
    clt
    wbr
    #
    @78
    wa
    #
    @77
    @76
    @59
    @79
    @78
    @59
    cA
    @30
    clt
    wbr
    #
    @79
    @58
    @81
    @79
    wa
    @57
    @30
    cA
    cB
    eliooord
    adantl
    #
    simprd
    biantrurd
    @59
    @30
    cA
    @19
    @59
    @0
    cr
    @30
    cA
    cB
    ioossre
    #
    @57
    @58
    simpr
    sseldi
    #
    wph
    cA
    cr
    wcel
    #
    @45
    @56
    @58
    lhop1.a
    ad3antrrr
    #
    @57
    @19
    cr
    wcel
    #
    @58
    @57
    @19
    @46
    @56
    simpr
    rpred
    #
    adantr
    ltsubaddd
    @59
    @30
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @69
    cxr
    wcel
    #
    @76
    @80
    wb
    @59
    @30
    @84
    rexrd
    #
    wph
    @90
    @45
    @56
    @58
    lhop1.b
    ad3antrrr
    #
    @57
    @91
    @58
    @57
    @69
    @57
    @19
    cA
    @88
    wph
    @85
    @45
    @56
    lhop1.a
    ad2antrr
    readdcld
    rexrd
    #
    adantr
    #
    @30
    cB
    @69
    xrltmin
    syl3anc
    3bitr4rd
    @59
    cA
    cxr
    wcel
    #
    @71
    cxr
    wcel
    #
    @89
    @81
    @73
    @76
    wb
    @59
    cA
    @86
    rexrd
    @59
    @70
    cB
    @69
    cxr
    @93
    @95
    ifcld
    @92
    @59
    @81
    @79
    @82
    simpld
    #
    @96
    @97
    @89
    w3a
    @73
    @81
    @76
    cA
    @71
    @30
    elioo5
    baibd
    syl31anc
    @59
    @33
    @32
    @19
    clt
    @59
    cA
    @30
    @86
    @84
    @59
    cA
    @30
    @86
    @84
    @98
    ltled
    abssubge0d
    breq1d
    3bitr4d
    rabbi2dva
    @57
    @72
    @0
    wss
    #
    @75
    @72
    wceq
    @57
    @90
    @71
    cB
    cle
    wbr
    #
    @99
    wph
    @90
    @45
    @56
    lhop1.b
    ad2antrr
    #
    @57
    @90
    @91
    @100
    @101
    @94
    cB
    @69
    xrmin1
    #
    syl2anc
    cA
    @71
    cB
    iooss2
    syl2anc
    @72
    @0
    sseqin2
    sylib
    eqtr3d
    #
    eleq2d
    syl5bbr
    @46
    @56
    @73
    @67
    @50
    @15
    @2
    cfv
    #
    @15
    @4
    cfv
    #
    cdiv
    co
    #
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @47
    clt
    wbr
    #
    vy
    @74
    wral
    #
    @46
    @56
    @73
    wa
    #
    wa
    #
    @66
    @50
    @20
    @109
    wi
    #
    vy
    @0
    wral
    @110
    @49
    @113
    vy
    @0
    @15
    @0
    wcel
    #
    @21
    @20
    @48
    @109
    @114
    @20
    @21
    @114
    @16
    @20
    @114
    @15
    cA
    @15
    cA
    wceq
    @114
    cA
    @0
    wcel
    cA
    cB
    lbioo
    @15
    cA
    @0
    eleq1
    mtbiri
    necon2ai
    biantrurd
    bicomd
    @114
    @24
    @108
    @47
    clt
    @114
    @23
    @107
    cabs
    @114
    @22
    @106
    cC
    cmin
    vz
    @15
    @6
    @106
    @0
    @7
    vz
    vy
    weq
    @3
    @104
    @5
    @105
    cdiv
    @1
    @15
    @2
    fveq2
    @1
    @15
    @4
    fveq2
    oveq12d
    @7
    eqid
    #
    @3
    @5
    cdiv
    ovex
    fvmpt3i
    oveq1d
    fveq2d
    breq1d
    imbi12d
    ralbiia
    @34
    @20
    @109
    vy
    vv
    @0
    vv
    vy
    weq
    #
    @33
    @18
    @19
    clt
    @116
    @32
    @17
    cabs
    @30
    @15
    cA
    cmin
    oveq1
    fveq2d
    breq1d
    ralrab
    bitr4i
    @112
    @110
    @109
    vy
    @72
    wral
    #
    @66
    @112
    @109
    vy
    @74
    @72
    @46
    @56
    @74
    @72
    wceq
    @73
    @103
    adantrr
    raleqdv
    @46
    @111
    @117
    @66
    @46
    @111
    @117
    wa
    #
    wa
    #
    @65
    c2
    @47
    cmul
    co
    #
    @39
    clt
    @119
    vz
    vy
    cA
    cB
    cC
    @71
    cA
    vr
    cv
    c2
    cdiv
    co
    caddc
    co
    #
    @47
    cF
    cG
    @30
    vr
    wph
    @85
    @45
    @118
    lhop1.a
    ad2antrr
    #
    wph
    @90
    @45
    @118
    lhop1.b
    ad2antrr
    #
    wph
    cA
    cB
    clt
    wbr
    #
    @45
    @118
    lhop1.l
    ad2antrr
    #
    wph
    @0
    cr
    cF
    wf
    @45
    @118
    lhop1.f
    ad2antrr
    wph
    @0
    cr
    cG
    wf
    #
    @45
    @118
    lhop1.g
    ad2antrr
    wph
    @2
    cdm
    #
    @0
    wceq
    @45
    @118
    lhop1.if
    ad2antrr
    wph
    @4
    cdm
    #
    @0
    wceq
    @45
    @118
    lhop1.ig
    ad2antrr
    wph
    cc0
    cF
    cA
    climc
    co
    wcel
    @45
    @118
    lhop1.f0
    ad2antrr
    wph
    cc0
    cG
    cA
    climc
    co
    wcel
    @45
    @118
    lhop1.g0
    ad2antrr
    wph
    cc0
    cG
    crn
    #
    wcel
    #
    wn
    #
    @45
    @118
    lhop1.gn0
    ad2antrr
    wph
    cc0
    @4
    crn
    #
    wcel
    #
    wn
    #
    @45
    @118
    lhop1.gd0
    ad2antrr
    wph
    @8
    @45
    @118
    lhop1.c
    ad2antrr
    @46
    @52
    @118
    @54
    adantr
    @119
    cA
    @69
    cioc
    co
    #
    cr
    @71
    @119
    @96
    @69
    cr
    wcel
    @135
    cr
    wss
    @119
    cA
    @122
    rexrd
    #
    @119
    @19
    cA
    @119
    @19
    @46
    @56
    @73
    @117
    simprll
    #
    rpred
    #
    @122
    readdcld
    #
    cA
    @69
    iocssre
    syl2anc
    @119
    @71
    @135
    wcel
    #
    @97
    cA
    @71
    clt
    wbr
    #
    @71
    @69
    cle
    wbr
    #
    @119
    @70
    cB
    @69
    cxr
    @119
    @90
    @70
    @123
    adantr
    @119
    @70
    wn
    #
    wa
    #
    @69
    @144
    @19
    cA
    @119
    @87
    @143
    @138
    adantr
    @119
    @85
    @143
    @122
    adantr
    readdcld
    rexrd
    ifclda
    @119
    @141
    @124
    cA
    @69
    clt
    wbr
    #
    @125
    @119
    cA
    @19
    @122
    @137
    ltaddrp2d
    @119
    @96
    @90
    @91
    @141
    @124
    @145
    wa
    wb
    @136
    @123
    @119
    @69
    @139
    rexrd
    #
    cA
    cB
    @69
    xrltmin
    syl3anc
    mpbir2and
    @119
    @90
    @91
    @142
    @123
    @146
    cB
    @69
    xrmin2
    syl2anc
    @119
    @96
    @91
    @140
    @97
    @141
    @142
    w3a
    wb
    @136
    @146
    cA
    @69
    @71
    elioc1
    syl2anc
    mpbir3and
    sseldd
    @119
    @90
    @91
    @100
    @123
    @146
    @102
    syl2anc
    @46
    @56
    @73
    @117
    simprlr
    @46
    @111
    @117
    simprr
    @121
    eqid
    lhop1lem
    @46
    @120
    @39
    wceq
    @118
    @46
    @39
    c2
    @46
    @39
    @53
    rpcnd
    @46
    2cnd
    c2
    cc0
    wne
    @46
    2ne0
    a1i
    divcan2d
    adantr
    breqtrd
    expr
    sylbid
    syl5bi
    expr
    sylbid
    expdimp
    @58
    @60
    @67
    wb
    @57
    @58
    @40
    @66
    @50
    @58
    @38
    @65
    @39
    clt
    @58
    @37
    @64
    cabs
    @58
    @36
    @63
    cC
    cmin
    vz
    @30
    @11
    @63
    @0
    @12
    vz
    vv
    weq
    @9
    @61
    @10
    @62
    cdiv
    @1
    @30
    cF
    fveq2
    @1
    @30
    cG
    fveq2
    oveq12d
    @12
    eqid
    #
    @9
    @10
    cdiv
    ovex
    fvmpt3i
    oveq1d
    fveq2d
    breq1d
    imbi2d
    adantl
    sylibrd
    adantld
    com23
    ralrimdva
    reximdva
    syld
    ralrimdva
    anim2d
    wph
    ve
    vd
    vy
    @0
    cA
    cC
    @7
    wph
    vz
    @0
    @6
    cc
    @7
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    @5
    wph
    @0
    cc
    @1
    @2
    wph
    @127
    cc
    @2
    wf
    @0
    cc
    @2
    wf
    cF
    dvf
    wph
    @127
    @0
    cc
    @2
    lhop1.if
    feq2d
    mpbii
    ffvelrnda
    wph
    @0
    cc
    @1
    @4
    wph
    @128
    cc
    @4
    wf
    @0
    cc
    @4
    wf
    #
    cG
    dvf
    wph
    @128
    @0
    cc
    @4
    lhop1.ig
    feq2d
    mpbii
    #
    ffvelrnda
    @149
    @134
    @5
    cc0
    wne
    wph
    @134
    @148
    lhop1.gd0
    adantr
    @149
    @133
    @5
    cc0
    @149
    @5
    @132
    wcel
    #
    @5
    cc0
    wceq
    @133
    wph
    @4
    @0
    wfn
    #
    @148
    @152
    wph
    @150
    @153
    @151
    @0
    cc
    @4
    ffn
    syl
    @0
    @1
    @4
    fnfvelrn
    sylan
    @5
    cc0
    @132
    eleq1
    syl5ibcom
    necon3bd
    mpd
    divcld
    @115
    fmptd
    @0
    cc
    wss
    wph
    @0
    cr
    cc
    @83
    ax-resscn
    sstri
    a1i
    #
    wph
    cA
    lhop1.a
    recnd
    #
    ellimc3
    wph
    vx
    vd
    vv
    @0
    cA
    cC
    @12
    wph
    vz
    @0
    @11
    cc
    @12
    @149
    @9
    @10
    @149
    @9
    wph
    @0
    cr
    @1
    cF
    lhop1.f
    ffvelrnda
    recnd
    @149
    @10
    wph
    @0
    cr
    @1
    cG
    lhop1.g
    ffvelrnda
    recnd
    @149
    @131
    @10
    cc0
    wne
    wph
    @131
    @148
    lhop1.gn0
    adantr
    @149
    @130
    @10
    cc0
    @149
    @10
    @129
    wcel
    #
    @10
    cc0
    wceq
    @130
    wph
    cG
    @0
    wfn
    #
    @148
    @156
    wph
    @126
    @157
    lhop1.g
    @0
    cr
    cG
    ffn
    syl
    @0
    @1
    cG
    fnfvelrn
    sylan
    @10
    cc0
    @129
    eleq1
    syl5ibcom
    necon3bd
    mpd
    divcld
    @147
    fmptd
    @154
    @155
    ellimc3
    3imtr4d
    mpd
end
