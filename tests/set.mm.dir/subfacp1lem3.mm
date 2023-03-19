include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "cres.mm"
include "cop.mm"
include "cpr.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "cfn.mm"
include "wss.mm"
include "caddc.mm"
include "cfz.mm"
include "wf1o.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "fzfi.mm"
include "deranglem.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "mp2an.mm"
include "elexi.mm"
include "a1i.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "diffi.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "wf1.mm"
include "simpr.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "vex.mm"
include "f1oeq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "elab2.mm"
include "f1of1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "3syl.mm"
include "wfn.mm"
include "wb.mm"
include "f1ofn.mm"
include "syl.mm"
include "fnresdm.mm"
include "mpbird.mm"
include "f1ofo.mm"
include "wrex.mm"
include "ssun2.mm"
include "cin.mm"
include "c0.mm"
include "subfacp1lem1.mm"
include "simp2d.mm"
include "syl5sseq.mm"
include "adantr.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "simprd.mm"
include "prid2.mm"
include "syl6eqel.mm"
include "1ex.mm"
include "prid1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ralpr.mm"
include "sylanbrc.mm"
include "fvres.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "ffnfv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "eqcom.mm"
include "syl5bb.mm"
include "rexbiia.mm"
include "ralbii.mm"
include "dffo3.mm"
include "resdif.mm"
include "syl3anc.mm"
include "uncom.mm"
include "syl5eq.mm"
include "incom.mm"
include "simp1d.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "reseq2.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "3bitrd.mm"
include "ssun1.mm"
include "ssralv.mm"
include "sylc.mm"
include "resex.mm"
include "sylan9eq.mm"
include "ralbidva.mm"
include "ex.mm"
include "cn.mm"
include "eqid.mm"
include "subfacp1lem2a.mm"
include "subfacp1lem2b.mm"
include "r19.21bi.mm"
include "eqnetrd.mm"
include "ralrimiva.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eluz2b3.mm"
include "simp3d.mm"
include "necomd.mm"
include "id.mm"
include "neeq12d.mm"
include "ralunb.mm"
include "raleqdv.mm"
include "prex.mm"
include "unex.mm"
include "jca.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqtr4d.mm"
include "eqeq12d.mm"
include "biantrud.mm"
include "syl6bbr.mm"
include "eqeq2d.mm"
include "3bitr3rd.mm"
include "syl6bb.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"
include "en3d.mm"
include "hashen.mm"
include "fveq2i.mm"
include "derangval.mm"
include "derangen2.mm"
include "3eqtr2ri.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem subfacp1lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let cK: class K
  let cM: class M
  let cN: class N
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }
  assume subfacp1lem1.n: |- ( ph -> N e. NN )
  assume subfacp1lem1.m: |- ( ph -> M e. ( 2 ... ( N + 1 ) ) )
  assume subfacp1lem1.x: |- M e. _V
  assume subfacp1lem1.k: |- K = ( ( 2 ... ( N + 1 ) ) \ { M } )
  assume subfacp1lem3.b: |- B = { g e. A | ( ( g ` 1 ) = M /\ ( g ` M ) = 1 ) }
  assume subfacp1lem3.c: |- C = { f | ( f : K -1-1-onto-> K /\ A. y e. K ( f ` y ) =/= y ) }

  disjoint f g
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N f
  disjoint N g
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g s
  disjoint g z
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint g k
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B h
  disjoint B s
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint b ph
  disjoint c ph
  disjoint K c
  disjoint M b
  disjoint S m
  disjoint V f
  assert |- ( ph -> ( # ` B ) = ( S ` ( N - 1 ) ) )

  proof
    wph
    cB
    chash
    cfv
    #
    cC
    chash
    cfv
    #
    cN
    c1
    cmin
    co
    #
    cS
    cfv
    #
    wph
    cB
    cC
    cen
    wbr
    #
    @0
    @1
    wceq
    #
    wph
    vb
    vc
    cB
    cC
    vb
    cv
    #
    cK
    cres
    #
    vc
    cv
    #
    c1
    cM
    cop
    #
    cM
    c1
    cop
    #
    cpr
    #
    cun
    #
    cB
    cvv
    wcel
    wph
    cB
    cfn
    cA
    cfn
    wcel
    cB
    cA
    wss
    cB
    cfn
    wcel
    #
    cA
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    @15
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @16
    cfv
    #
    @18
    wne
    #
    vy
    @15
    wral
    #
    wa
    #
    vf
    cab
    #
    cfn
    subfacp1lem.a
    @15
    cfn
    wcel
    @23
    cfn
    wcel
    c1
    @14
    fzfi
    @21
    @15
    vf
    deranglem
    ax-mp
    eqeltri
    cB
    c1
    vg
    cv
    #
    cfv
    #
    cM
    wceq
    #
    cM
    @24
    cfv
    #
    c1
    wceq
    #
    wa
    #
    vg
    cA
    crab
    cA
    subfacp1lem3.b
    @29
    vg
    cA
    ssrab2
    eqsstri
    cA
    cB
    ssfi
    mp2an
    #
    elexi
    a1i
    cC
    cvv
    wcel
    wph
    cC
    cfn
    cC
    cK
    cK
    @16
    wf1o
    #
    @20
    vy
    cK
    wral
    #
    wa
    #
    vf
    cab
    #
    cfn
    subfacp1lem3.c
    cK
    cfn
    wcel
    #
    @34
    cfn
    wcel
    cK
    c2
    @14
    cfz
    co
    #
    cM
    csn
    #
    cdif
    #
    cfn
    subfacp1lem1.k
    @36
    cfn
    wcel
    @38
    cfn
    wcel
    c2
    @14
    fzfi
    @36
    @37
    diffi
    ax-mp
    eqeltri
    #
    @32
    cK
    vf
    deranglem
    ax-mp
    eqeltri
    #
    elexi
    a1i
    wph
    @6
    cB
    wcel
    #
    @7
    cC
    wcel
    #
    wph
    @41
    wa
    #
    cK
    cK
    @7
    wf1o
    #
    @18
    @6
    cfv
    #
    @18
    wne
    #
    vy
    cK
    wral
    #
    @42
    @43
    @15
    c1
    cM
    cpr
    #
    cdif
    #
    @49
    @6
    @49
    cres
    #
    wf1o
    #
    @44
    @43
    @6
    ccnv
    wfun
    #
    @15
    @15
    @6
    @15
    cres
    #
    wfo
    #
    @48
    @48
    @6
    @48
    cres
    #
    wfo
    #
    @51
    @43
    @15
    @15
    @6
    wf1o
    #
    @15
    @15
    @6
    wf1
    #
    @52
    @43
    @57
    @46
    vy
    @15
    wral
    #
    @43
    @6
    cA
    wcel
    #
    @57
    @59
    wa
    #
    @43
    @60
    c1
    @6
    cfv
    #
    cM
    wceq
    #
    cM
    @6
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @43
    @41
    @60
    @66
    wa
    wph
    @41
    simpr
    @29
    @66
    vg
    @6
    cA
    cB
    vg
    vb
    weq
    #
    @26
    @63
    @28
    @65
    @67
    @25
    @62
    cM
    c1
    @24
    @6
    fveq1
    eqeq1d
    @67
    @27
    @64
    c1
    cM
    @24
    @6
    fveq1
    eqeq1d
    anbi12d
    subfacp1lem3.b
    elrab2
    sylib
    #
    simpld
    @22
    @61
    vf
    @6
    cA
    vb
    vex
    #
    vf
    vb
    weq
    #
    @17
    @57
    @21
    @59
    @15
    @15
    @16
    @6
    f1oeq1
    @70
    @20
    @46
    vy
    @15
    @70
    @19
    @45
    @18
    @18
    @16
    @6
    fveq1
    neeq1d
    ralbidv
    anbi12d
    subfacp1lem.a
    elab2
    sylib
    #
    simpld
    #
    @15
    @15
    @6
    f1of1
    @58
    @15
    @15
    @6
    wf
    @52
    @15
    @15
    @6
    df-f1
    simprbi
    3syl
    @43
    @15
    @15
    @53
    wf1o
    #
    @54
    @43
    @73
    @57
    @72
    @43
    @6
    @15
    wfn
    #
    @53
    @6
    wceq
    @73
    @57
    wb
    @43
    @57
    @74
    @72
    @15
    @15
    @6
    f1ofn
    syl
    #
    @15
    @6
    fnresdm
    @15
    @15
    @53
    @6
    f1oeq1
    3syl
    mpbird
    @15
    @15
    @53
    f1ofo
    syl
    @43
    @48
    @48
    @55
    wf
    #
    vx
    cv
    #
    @18
    @55
    cfv
    #
    wceq
    #
    vy
    @48
    wrex
    #
    vx
    @48
    wral
    #
    @56
    @43
    @55
    @48
    wfn
    #
    @77
    @55
    cfv
    #
    @48
    wcel
    #
    vx
    @48
    wral
    #
    @76
    @43
    @74
    @48
    @15
    wss
    #
    @82
    @75
    wph
    @86
    @41
    wph
    cK
    @48
    cun
    #
    @48
    @15
    @48
    cK
    ssun2
    wph
    cK
    @48
    cin
    #
    c0
    wceq
    #
    @87
    @15
    wceq
    #
    cK
    chash
    cfv
    #
    @2
    wceq
    #
    wph
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    cK
    cM
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    subfacp1lem1.n
    subfacp1lem1.m
    subfacp1lem1.x
    subfacp1lem1.k
    subfacp1lem1
    #
    simp2d
    #
    syl5sseq
    #
    adantr
    @15
    @48
    @6
    fnssres
    syl2anc
    @43
    @77
    @6
    cfv
    #
    @48
    wcel
    #
    vx
    @48
    wral
    #
    @85
    @43
    @62
    @48
    wcel
    #
    @64
    @48
    wcel
    #
    @98
    @43
    @62
    cM
    @48
    @43
    @63
    @65
    @43
    @60
    @66
    @68
    simprd
    #
    simpld
    #
    c1
    cM
    subfacp1lem1.x
    prid2
    #
    syl6eqel
    @43
    @64
    c1
    @48
    @43
    @63
    @65
    @101
    simprd
    #
    c1
    cM
    1ex
    prid1
    #
    syl6eqel
    @97
    @99
    @100
    vx
    c1
    cM
    1ex
    subfacp1lem1.x
    @77
    c1
    wceq
    #
    @96
    @62
    @48
    @77
    c1
    @6
    fveq2
    eleq1d
    @77
    cM
    wceq
    #
    @96
    @64
    @48
    @77
    cM
    @6
    fveq2
    eleq1d
    ralpr
    sylanbrc
    @84
    @97
    vx
    @48
    @77
    @48
    wcel
    @83
    @96
    @48
    @77
    @48
    @6
    fvres
    eleq1d
    ralbiia
    sylibr
    vx
    @48
    @48
    @55
    ffnfv
    sylanbrc
    @43
    @45
    @77
    wceq
    #
    vy
    @48
    wrex
    #
    vx
    @48
    wral
    #
    @81
    @43
    @45
    c1
    wceq
    #
    vy
    @48
    wrex
    #
    @45
    cM
    wceq
    #
    vy
    @48
    wrex
    #
    @110
    @43
    cM
    @48
    wcel
    @65
    @112
    @103
    @104
    @111
    @65
    vy
    cM
    @48
    @18
    cM
    wceq
    #
    @45
    @64
    c1
    @18
    cM
    @6
    fveq2
    #
    eqeq1d
    rspcev
    sylancr
    @43
    c1
    @48
    wcel
    @63
    @114
    @105
    @102
    @113
    @63
    vy
    c1
    @48
    @18
    c1
    wceq
    #
    @45
    @62
    cM
    @18
    c1
    @6
    fveq2
    #
    eqeq1d
    rspcev
    sylancr
    @109
    @112
    @114
    vx
    c1
    cM
    1ex
    subfacp1lem1.x
    @106
    @108
    @111
    vy
    @48
    @77
    c1
    @45
    eqeq2
    rexbidv
    @107
    @108
    @113
    vy
    @48
    @77
    cM
    @45
    eqeq2
    rexbidv
    ralpr
    sylanbrc
    @80
    @109
    vx
    @48
    @79
    @108
    vy
    @48
    @79
    @78
    @77
    wceq
    @18
    @48
    wcel
    #
    @108
    @77
    @78
    eqcom
    @119
    @78
    @45
    @77
    @18
    @48
    @6
    fvres
    eqeq1d
    syl5bb
    rexbiia
    ralbii
    sylibr
    vy
    vx
    @48
    @48
    @55
    dffo3
    sylanbrc
    @15
    @48
    @15
    @48
    @6
    resdif
    syl3anc
    @43
    @49
    cK
    wceq
    #
    @51
    @44
    wb
    wph
    @120
    @41
    wph
    @48
    cK
    cun
    #
    @15
    wceq
    #
    @120
    wph
    @121
    @87
    @15
    @48
    cK
    uncom
    @94
    syl5eq
    wph
    @86
    @48
    cK
    cin
    #
    c0
    wceq
    @122
    @120
    wb
    @95
    wph
    @123
    @88
    c0
    @48
    cK
    incom
    wph
    @89
    @90
    @92
    @93
    simp1d
    syl5eq
    @48
    cK
    @15
    uneqdifeq
    syl2anc
    mpbid
    adantr
    @120
    @51
    @49
    @49
    @7
    wf1o
    #
    cK
    @49
    @7
    wf1o
    @44
    @120
    @50
    @7
    wceq
    @51
    @124
    wb
    @49
    cK
    @6
    reseq2
    @49
    @49
    @50
    @7
    f1oeq1
    syl
    @49
    cK
    @49
    @7
    f1oeq2
    @49
    cK
    cK
    @7
    f1oeq3
    3bitrd
    syl
    mpbid
    @43
    cK
    @15
    wss
    #
    @59
    @47
    wph
    @125
    @41
    wph
    @87
    cK
    @15
    cK
    @48
    ssun1
    @94
    syl5sseq
    #
    adantr
    @43
    @57
    @59
    @71
    simprd
    @46
    vy
    cK
    @15
    ssralv
    sylc
    @33
    @44
    @47
    wa
    vf
    @7
    cC
    @6
    cK
    @69
    resex
    @16
    @7
    wceq
    #
    @31
    @44
    @32
    @47
    cK
    cK
    @16
    @7
    f1oeq1
    @127
    @20
    @46
    vy
    cK
    @127
    @18
    cK
    wcel
    #
    wa
    @19
    @45
    @18
    @127
    @128
    @19
    @18
    @7
    cfv
    #
    @45
    @18
    @16
    @7
    fveq1
    @18
    cK
    @6
    fvres
    #
    sylan9eq
    neeq1d
    ralbidva
    anbi12d
    subfacp1lem3.c
    elab2
    sylanbrc
    ex
    wph
    @8
    cC
    wcel
    #
    @12
    cB
    wcel
    #
    wph
    @131
    wa
    #
    @12
    cA
    wcel
    #
    c1
    @12
    cfv
    #
    cM
    wceq
    #
    cM
    @12
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @132
    @133
    @15
    @15
    @12
    wf1o
    #
    @18
    @12
    cfv
    #
    @18
    wne
    #
    vy
    @15
    wral
    #
    @134
    @133
    @140
    @136
    @138
    @133
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    @12
    @8
    cK
    cM
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    wph
    cN
    cn
    wcel
    @131
    subfacp1lem1.n
    adantr
    #
    wph
    cM
    @36
    wcel
    #
    @131
    subfacp1lem1.m
    adantr
    #
    subfacp1lem1.x
    subfacp1lem1.k
    @12
    eqid
    #
    @133
    cK
    cK
    @8
    wf1o
    #
    @18
    @8
    cfv
    #
    @18
    wne
    #
    vy
    cK
    wral
    #
    @133
    @131
    @148
    @151
    wa
    #
    wph
    @131
    simpr
    @33
    @152
    vf
    @8
    cC
    vc
    vex
    #
    vf
    vc
    weq
    #
    @31
    @148
    @32
    @151
    cK
    cK
    @16
    @8
    f1oeq1
    @154
    @20
    @150
    vy
    cK
    @154
    @19
    @149
    @18
    @18
    @16
    @8
    fveq1
    neeq1d
    ralbidv
    anbi12d
    subfacp1lem3.c
    elab2
    sylib
    #
    simpld
    #
    subfacp1lem2a
    #
    simp1d
    #
    @133
    @142
    vy
    @87
    wral
    #
    @143
    @133
    @142
    vy
    cK
    wral
    @142
    vy
    @48
    wral
    #
    @159
    @133
    @142
    vy
    cK
    @133
    @128
    wa
    #
    @141
    @149
    @18
    @133
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    @12
    @8
    cK
    cM
    cN
    @18
    derang.d
    subfac.n
    subfacp1lem.a
    @144
    @146
    subfacp1lem1.x
    subfacp1lem1.k
    @147
    @156
    subfacp1lem2b
    #
    @133
    @150
    vy
    cK
    @133
    @148
    @151
    @155
    simprd
    r19.21bi
    eqnetrd
    ralrimiva
    @133
    @135
    c1
    wne
    #
    @137
    cM
    wne
    #
    @160
    @133
    @135
    cM
    c1
    @133
    @140
    @136
    @138
    @157
    simp2d
    #
    wph
    cM
    c1
    wne
    #
    @131
    wph
    @145
    cM
    c2
    cuz
    cfv
    wcel
    #
    @166
    subfacp1lem1.m
    cM
    c2
    @14
    elfzuz
    @167
    cM
    cn
    wcel
    @166
    cM
    eluz2b3
    simprbi
    3syl
    adantr
    #
    eqnetrd
    @133
    @137
    c1
    cM
    @133
    @140
    @136
    @138
    @157
    simp3d
    #
    @133
    cM
    c1
    @168
    necomd
    eqnetrd
    @142
    @163
    @164
    vy
    c1
    cM
    1ex
    subfacp1lem1.x
    @117
    @141
    @135
    @18
    c1
    @18
    c1
    @12
    fveq2
    #
    @117
    id
    neeq12d
    @115
    @141
    @137
    @18
    cM
    @18
    cM
    @12
    fveq2
    #
    @115
    id
    neeq12d
    ralpr
    sylanbrc
    @142
    vy
    cK
    @48
    ralunb
    sylanbrc
    @133
    @142
    vy
    @87
    @15
    wph
    @90
    @131
    @94
    adantr
    raleqdv
    mpbid
    @22
    @140
    @143
    wa
    vf
    @12
    cA
    @8
    @11
    @153
    @9
    @10
    prex
    unex
    @16
    @12
    wceq
    #
    @17
    @140
    @21
    @143
    @15
    @15
    @16
    @12
    f1oeq1
    @172
    @20
    @142
    vy
    @15
    @172
    @19
    @141
    @18
    @18
    @16
    @12
    fveq1
    neeq1d
    ralbidv
    anbi12d
    subfacp1lem.a
    elab2
    sylanbrc
    @133
    @136
    @138
    @165
    @169
    jca
    @29
    @139
    vg
    @12
    cA
    cB
    @24
    @12
    wceq
    #
    @26
    @136
    @28
    @138
    @173
    @25
    @135
    cM
    c1
    @24
    @12
    fveq1
    eqeq1d
    @173
    @27
    @137
    c1
    cM
    @24
    @12
    fveq1
    eqeq1d
    anbi12d
    subfacp1lem3.b
    elrab2
    sylanbrc
    ex
    wph
    @41
    @131
    wa
    #
    @6
    @12
    wceq
    #
    @8
    @7
    wceq
    #
    wb
    wph
    @174
    wa
    #
    @45
    @141
    wceq
    #
    vy
    @15
    wral
    #
    @149
    @129
    wceq
    #
    vy
    cK
    wral
    #
    @175
    @176
    @177
    @179
    @45
    @149
    wceq
    #
    vy
    cK
    wral
    #
    @181
    @177
    @178
    vy
    cK
    wral
    #
    @178
    vy
    @87
    wral
    #
    @183
    @179
    @177
    @184
    @184
    @178
    vy
    @48
    wral
    #
    wa
    @185
    @177
    @186
    @184
    @177
    @62
    @135
    wceq
    #
    @64
    @137
    wceq
    #
    @186
    @177
    @62
    cM
    @135
    wph
    @41
    @63
    @131
    @102
    adantrr
    wph
    @131
    @136
    @41
    @165
    adantrl
    eqtr4d
    @177
    @64
    c1
    @137
    wph
    @41
    @65
    @131
    @104
    adantrr
    wph
    @131
    @138
    @41
    @169
    adantrl
    eqtr4d
    @178
    @187
    @188
    vy
    c1
    cM
    1ex
    subfacp1lem1.x
    @117
    @45
    @62
    @141
    @135
    @118
    @170
    eqeq12d
    @115
    @45
    @64
    @141
    @137
    @116
    @171
    eqeq12d
    ralpr
    sylanbrc
    biantrud
    @178
    vy
    cK
    @48
    ralunb
    syl6bbr
    wph
    @131
    @184
    @183
    wb
    @41
    @133
    @178
    @182
    vy
    cK
    @161
    @141
    @149
    @45
    @162
    eqeq2d
    ralbidva
    adantrl
    @177
    @178
    vy
    @87
    @15
    wph
    @90
    @174
    @94
    adantr
    raleqdv
    3bitr3rd
    @180
    @182
    vy
    cK
    @128
    @180
    @149
    @45
    wceq
    @182
    @128
    @129
    @45
    @149
    @130
    eqeq2d
    @149
    @45
    eqcom
    syl6bb
    ralbiia
    syl6bbr
    @177
    @74
    @12
    @15
    wfn
    #
    @175
    @179
    wb
    wph
    @41
    @74
    @131
    @75
    adantrr
    #
    @177
    @140
    @189
    wph
    @131
    @140
    @41
    @158
    adantrl
    @15
    @15
    @12
    f1ofn
    syl
    vy
    @15
    @6
    @12
    eqfnfv
    syl2anc
    @177
    @8
    cK
    wfn
    #
    @7
    cK
    wfn
    #
    @176
    @181
    wb
    @177
    @148
    @191
    wph
    @131
    @148
    @41
    @156
    adantrl
    cK
    cK
    @8
    f1ofn
    syl
    @177
    @74
    @125
    @192
    @190
    wph
    @125
    @174
    @126
    adantr
    @15
    cK
    @6
    fnssres
    syl2anc
    vy
    cK
    @8
    @7
    eqfnfv
    syl2anc
    3bitr4d
    ex
    en3d
    @13
    cC
    cfn
    wcel
    @5
    @4
    wb
    @30
    @40
    cB
    cC
    hashen
    mp2an
    sylibr
    wph
    @1
    @91
    cS
    cfv
    #
    @3
    @1
    @34
    chash
    cfv
    #
    cK
    cD
    cfv
    #
    @193
    cC
    @34
    chash
    subfacp1lem3.c
    fveq2i
    @35
    @195
    @194
    wceq
    @39
    vx
    vy
    cK
    cD
    vf
    derang.d
    derangval
    ax-mp
    @35
    @195
    @193
    wceq
    @39
    vx
    vy
    cK
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    derangen2
    ax-mp
    3eqtr2ri
    wph
    @91
    @2
    cS
    wph
    @89
    @90
    @92
    @93
    simp3d
    fveq2d
    syl5eqr
    eqtrd
end
