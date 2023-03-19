include "crn.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cv.mm"
include "cmul.mm"
include "wcel.mm"
include "cz.mm"
include "wrex.mm"
include "cicc.mm"
include "crab.mm"
include "cun.mm"
include "readdcld.mm"
include "cc0.mm"
include "clt.mm"
include "0red.mm"
include "ltadd1dd.mm"
include "recnd.mm"
include "addid2d.mm"
include "breqtrd.mm"
include "ltled.mm"
include "eqbrtrrd.mm"
include "eliccd.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "resubcld.mm"
include "cr.mm"
include "syl5eqel.mm"
include "wbr.mm"
include "lttrd.mm"
include "posdifd.mm"
include "mpbid.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "flcld.mm"
include "cmpt.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "zred.mm"
include "remulcld.mm"
include "fvmptd.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elun2.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "chash.mm"
include "c1.mm"
include "cfz.mm"
include "wiso.mm"
include "wfo.mm"
include "cfn.mm"
include "prfi.mm"
include "csn.mm"
include "cioc.mm"
include "wss.mm"
include "snfi.mm"
include "cres.mm"
include "wf1.mm"
include "wf.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fvres.mm"
include "simprbi.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfcri.mm"
include "nfan.mm"
include "simpl.mm"
include "cxr.mm"
include "rexrd.mm"
include "iocssre.mm"
include "adantr.mm"
include "elrabi.mm"
include "sseldd.mm"
include "w3a.mm"
include "simpr.mm"
include "wne.mm"
include "fvmpt2.mm"
include "ad2antrr.mm"
include "cle.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ad4ant14.mm"
include "jca31.mm"
include "iocssicc.mm"
include "fourierdlem4.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "iocgtlb.mm"
include "eqcomd.mm"
include "3brtr3d.mm"
include "zre.mm"
include "adantlr.mm"
include "simpllr.mm"
include "ltadd2d.mm"
include "mpbird.mm"
include "ad2antlr.mm"
include "crp.mm"
include "elrpd.mm"
include "ad3antrrr.mm"
include "ltmul1d.mm"
include "fvex.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "breq1.mm"
include "eqeq2d.mm"
include "simp-6l.mm"
include "simp-6r.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "simplr.mm"
include "fourierdlem6.mm"
include "chvarv.mm"
include "vtocl.mm"
include "syl21anc.mm"
include "cc.mm"
include "adddirp1d.mm"
include "addassd.mm"
include "subaddd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "3adantl3.mm"
include "wn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "sselda.mm"
include "3adant2.mm"
include "neqne.mm"
include "eliccelioc.mm"
include "mpbir2and.mm"
include "fourierdlem35.mm"
include "simpl3.mm"
include "pm2.61dan.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "eqid.mm"
include "fmptd.mm"
include "fssd.mm"
include "ssrab2.mm"
include "syl5ss.mm"
include "fssresd.mm"
include "feqmptd.mm"
include "feq1d.mm"
include "simplll.mm"
include "ad3antlr.mm"
include "jca.mm"
include "fourierdlem19.mm"
include "syl5eqss.mm"
include "lttri3d.mm"
include "ex.mm"
include "ralrimiva.mm"
include "dff13.mm"
include "f1fi.mm"
include "unfi.mm"
include "sylancr.mm"
include "velsn.mm"
include "elun1.mm"
include "sylbir.mm"
include "iccssred.mm"
include "iccgelb.mm"
include "leneltd.mm"
include "iccleub.mm"
include "eliocd.mm"
include "dfss3.mm"
include "sylibr.mm"
include "ssfi.mm"
include "prssi.mm"
include "unssd.mm"
include "fourierdlem36.mm"
include "wf1o.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "eleqtrrd.mm"

theorem fourierdlem51
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cH: class H
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  assume fourierdlem51.a: |- ( ph -> A e. RR )
  assume fourierdlem51.b: |- ( ph -> B e. RR )
  assume fourierdlem51.alt0: |- ( ph -> A < 0 )
  assume fourierdlem51.bgt0: |- ( ph -> 0 < B )
  assume fourierdlem51.t: |- T = ( B - A )
  assume fourierdlem51.cfi: |- ( ph -> C e. Fin )
  assume fourierdlem51.css: |- ( ph -> C C_ ( A [,] B ) )
  assume fourierdlem51.bc: |- ( ph -> B e. C )
  assume fourierdlem51.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem51.x: |- ( ph -> X e. RR )
  assume fourierdlem51.exc: |- ( ph -> ( E ` X ) e. C )
  assume fourierdlem51.d: |- D = ( { ( A + X ) , ( B + X ) } u. { y e. ( ( A + X ) [,] ( B + X ) ) | E. k e. ZZ ( y + ( k x. T ) ) e. C } )
  assume fourierdlem51.f: |- F = ( iota f f Isom < , < ( ( 0 ... ( ( # ` D ) - 1 ) ) , D ) )
  assume fourierdlem51.h: |- H = { y e. ( ( A + X ) (,] ( B + X ) ) | E. k e. ZZ ( y + ( k x. T ) ) e. C }

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint A y
  disjoint k y
  disjoint x y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint D f
  disjoint E k
  disjoint E x
  disjoint F f
  disjoint H x
  disjoint T k
  disjoint T x
  disjoint T y
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint f ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint j k
  disjoint j x
  disjoint A w
  disjoint A z
  disjoint k w
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B i
  disjoint B j
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint E w
  disjoint E z
  disjoint T i
  disjoint T j
  disjoint T w
  disjoint T z
  disjoint X w
  disjoint X z
  disjoint i ph
  disjoint j ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> X e. ran F )

  proof
    wph
    cX
    cD
    cF
    crn
    #
    wph
    cX
    cA
    cX
    caddc
    co
    #
    cB
    cX
    caddc
    co
    #
    cpr
    #
    vy
    cv
    #
    vk
    cv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cC
    wcel
    #
    vk
    cz
    wrex
    #
    vy
    @1
    @2
    cicc
    co
    #
    crab
    #
    cun
    #
    cD
    wph
    cX
    @11
    wcel
    #
    cX
    @12
    wcel
    wph
    cX
    @10
    wcel
    cX
    @6
    caddc
    co
    #
    cC
    wcel
    #
    vk
    cz
    wrex
    #
    @13
    wph
    @1
    @2
    cX
    wph
    cA
    cX
    fourierdlem51.a
    fourierdlem51.x
    readdcld
    #
    wph
    cB
    cX
    fourierdlem51.b
    fourierdlem51.x
    readdcld
    #
    fourierdlem51.x
    wph
    @1
    cX
    @17
    fourierdlem51.x
    wph
    @1
    cc0
    cX
    caddc
    co
    #
    cX
    clt
    wph
    cA
    cc0
    cX
    fourierdlem51.a
    wph
    0red
    #
    fourierdlem51.x
    fourierdlem51.alt0
    ltadd1dd
    wph
    cX
    wph
    cX
    fourierdlem51.x
    recnd
    addid2d
    #
    breqtrd
    ltled
    wph
    cX
    @2
    fourierdlem51.x
    @18
    wph
    @19
    cX
    @2
    clt
    @21
    wph
    cc0
    cB
    cX
    @20
    fourierdlem51.b
    fourierdlem51.x
    fourierdlem51.bgt0
    ltadd1dd
    eqbrtrrd
    ltled
    eliccd
    wph
    cB
    cX
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wcel
    cX
    @24
    cT
    cmul
    co
    #
    caddc
    co
    #
    cC
    wcel
    #
    @16
    wph
    @23
    wph
    @22
    cT
    wph
    cB
    cX
    fourierdlem51.b
    fourierdlem51.x
    resubcld
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem51.t
    wph
    cB
    cA
    fourierdlem51.b
    fourierdlem51.a
    resubcld
    syl5eqel
    #
    wph
    cT
    wph
    cc0
    @28
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    #
    cc0
    @28
    clt
    wbr
    wph
    cA
    cc0
    cB
    fourierdlem51.a
    @20
    fourierdlem51.b
    fourierdlem51.alt0
    fourierdlem51.bgt0
    lttrd
    #
    wph
    cA
    cB
    fourierdlem51.a
    fourierdlem51.b
    posdifd
    mpbid
    @28
    cT
    wceq
    #
    wph
    cT
    @28
    fourierdlem51.t
    eqcomi
    a1i
    #
    breqtrd
    #
    gt0ne0d
    #
    redivcld
    flcld
    #
    wph
    cX
    cE
    cfv
    @26
    cC
    wph
    vx
    cX
    vx
    cv
    #
    cB
    @37
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @26
    cr
    cE
    cr
    cE
    vx
    cr
    @42
    cmpt
    wceq
    wph
    fourierdlem51.e
    a1i
    @37
    cX
    wceq
    #
    @42
    @26
    wceq
    wph
    @43
    @37
    cX
    @41
    @25
    caddc
    @43
    id
    @43
    @40
    @24
    cT
    cmul
    @43
    @39
    @23
    cfl
    @43
    @38
    @22
    cT
    cdiv
    @37
    cX
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    fourierdlem51.x
    wph
    cX
    @25
    fourierdlem51.x
    wph
    @24
    cT
    wph
    @24
    @36
    zred
    @29
    remulcld
    readdcld
    fvmptd
    fourierdlem51.exc
    eqeltrrd
    @15
    @27
    vk
    @24
    cz
    @5
    @24
    wceq
    #
    @14
    @26
    cC
    @44
    @6
    @25
    cX
    caddc
    @5
    @24
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    rspcev
    syl2anc
    @9
    @16
    vy
    cX
    @10
    @4
    cX
    wceq
    #
    @8
    @15
    vk
    cz
    @45
    @7
    @14
    cC
    @4
    cX
    @6
    caddc
    oveq1
    eleq1d
    rexbidv
    elrab
    sylanbrc
    cX
    @11
    @3
    elun2
    syl
    fourierdlem51.d
    syl6eleqr
    wph
    cc0
    cD
    chash
    cfv
    c1
    cmin
    co
    #
    cfz
    co
    #
    cD
    clt
    clt
    cF
    wiso
    #
    @47
    cD
    cF
    wfo
    #
    @0
    cD
    wceq
    wph
    cD
    vf
    cF
    @46
    wph
    cD
    @12
    cfn
    fourierdlem51.d
    wph
    @3
    cfn
    wcel
    @11
    cfn
    wcel
    #
    @12
    cfn
    wcel
    @1
    @2
    prfi
    wph
    @1
    csn
    #
    @9
    vy
    @1
    @2
    cioc
    co
    #
    crab
    #
    cun
    #
    cfn
    wcel
    #
    @11
    @54
    wss
    #
    @50
    wph
    @51
    cfn
    wcel
    @53
    cfn
    wcel
    #
    @55
    @1
    snfi
    wph
    cC
    cfn
    wcel
    @53
    cC
    cE
    @53
    cres
    #
    wf1
    #
    @57
    fourierdlem51.cfi
    wph
    @53
    cC
    @58
    wf
    #
    vw
    cv
    #
    @58
    cfv
    #
    vz
    cv
    #
    @58
    cfv
    #
    wceq
    #
    @61
    @63
    wceq
    #
    wi
    #
    vz
    @53
    wral
    #
    vw
    @53
    wral
    @59
    wph
    @60
    @53
    cC
    vx
    @53
    @37
    @58
    cfv
    #
    cmpt
    #
    wf
    wph
    vx
    @53
    @69
    cC
    @70
    wph
    @37
    @53
    wcel
    #
    wa
    #
    @69
    @37
    cE
    cfv
    #
    cC
    @71
    @69
    @73
    wceq
    wph
    @37
    @53
    cE
    fvres
    adantl
    @72
    @37
    @6
    caddc
    co
    #
    cC
    wcel
    #
    vk
    cz
    wrex
    #
    @73
    cC
    wcel
    #
    @71
    @76
    wph
    @71
    @37
    @52
    wcel
    #
    @76
    @9
    @76
    vy
    @37
    @52
    @4
    @37
    wceq
    #
    @8
    @75
    vk
    cz
    @79
    @7
    @74
    cC
    @4
    @37
    @6
    caddc
    oveq1
    eleq1d
    rexbidv
    #
    elrab
    #
    simprbi
    adantl
    @72
    @75
    @77
    vk
    cz
    wph
    @71
    vk
    wph
    vk
    nfv
    vk
    vx
    @53
    @9
    vk
    vy
    @52
    @8
    vk
    cz
    nfre1
    vk
    @52
    nfcv
    nfrab
    nfcri
    nfan
    @77
    vk
    nfv
    @72
    wph
    @37
    cr
    wcel
    #
    @5
    cz
    wcel
    #
    @75
    @77
    wi
    wi
    wph
    @71
    simpl
    @72
    @52
    cr
    @37
    wph
    @52
    cr
    wss
    #
    @71
    wph
    @1
    cxr
    wcel
    #
    @2
    cr
    wcel
    #
    @84
    wph
    @1
    @17
    rexrd
    #
    @18
    @1
    @2
    iocssre
    syl2anc
    #
    adantr
    @71
    @78
    wph
    @9
    vy
    @37
    @52
    elrabi
    adantl
    sseldd
    wph
    @82
    wa
    #
    @83
    @75
    @77
    @89
    @83
    @75
    w3a
    #
    @74
    cA
    wceq
    #
    @77
    @89
    @83
    @91
    @77
    @75
    @89
    @83
    wa
    #
    @91
    wa
    #
    @73
    cB
    cC
    @93
    @73
    @42
    @37
    @5
    c1
    caddc
    co
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cB
    @89
    @73
    @42
    wceq
    #
    @83
    @91
    @89
    @82
    @42
    cr
    wcel
    @97
    wph
    @82
    simpr
    #
    @89
    @37
    @41
    @98
    @89
    @40
    cT
    @89
    @40
    @89
    @39
    @89
    @38
    cT
    @89
    cB
    @37
    wph
    cB
    cr
    wcel
    #
    @82
    fourierdlem51.b
    adantr
    #
    @98
    resubcld
    wph
    cT
    cr
    wcel
    #
    @82
    @29
    adantr
    #
    wph
    cT
    cc0
    wne
    @82
    @35
    adantr
    redivcld
    flcld
    #
    zred
    #
    @102
    remulcld
    #
    readdcld
    vx
    cr
    @42
    cr
    cE
    fourierdlem51.e
    fvmpt2
    syl2anc
    #
    ad2antrr
    #
    @93
    @41
    @95
    @37
    caddc
    @93
    @40
    @94
    cT
    cmul
    @93
    @92
    @40
    cz
    wcel
    #
    wa
    #
    @74
    cA
    cB
    cicc
    co
    #
    wcel
    #
    wa
    #
    @42
    @110
    wcel
    #
    @5
    @40
    clt
    wbr
    #
    @40
    @94
    wceq
    #
    @93
    @92
    @108
    @111
    @92
    @91
    simpl
    @89
    @108
    @83
    @91
    @103
    ad2antrr
    wph
    @91
    @111
    @82
    @83
    wph
    @91
    wa
    @74
    cA
    @110
    wph
    @91
    simpr
    wph
    cA
    @110
    wcel
    #
    @91
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    @116
    wph
    cA
    fourierdlem51.a
    rexrd
    #
    wph
    cB
    fourierdlem51.b
    rexrd
    wph
    cA
    cB
    fourierdlem51.a
    fourierdlem51.b
    @31
    ltled
    cA
    cB
    lbicc2
    syl3anc
    adantr
    eqeltrd
    ad4ant14
    jca31
    @89
    @113
    @83
    @91
    @89
    @73
    @42
    @110
    @106
    @89
    cA
    cB
    cioc
    co
    #
    @110
    @73
    cA
    cB
    iocssicc
    wph
    cr
    @120
    @37
    cE
    wph
    vx
    cA
    cB
    cT
    cE
    fourierdlem51.a
    fourierdlem51.b
    @31
    fourierdlem51.t
    fourierdlem51.e
    fourierdlem4
    #
    ffvelrnda
    #
    sseldi
    eqeltrrd
    ad2antrr
    @93
    @114
    @6
    @41
    clt
    wbr
    #
    @93
    @123
    @74
    @42
    clt
    wbr
    @93
    cA
    @73
    @74
    @42
    clt
    @89
    cA
    @73
    clt
    wbr
    #
    @83
    @91
    @89
    @117
    @118
    @73
    @120
    wcel
    @124
    wph
    @117
    @82
    @119
    adantr
    @89
    cB
    @100
    rexrd
    @122
    cA
    cB
    @73
    iocgtlb
    syl3anc
    ad2antrr
    @91
    cA
    @74
    wceq
    @92
    @91
    @74
    cA
    @91
    id
    eqcomd
    adantl
    @107
    3brtr3d
    @93
    @6
    @41
    @37
    @92
    @6
    cr
    wcel
    #
    @91
    wph
    @83
    @125
    @82
    wph
    @83
    wa
    #
    @5
    cT
    @83
    @5
    cr
    wcel
    #
    wph
    @5
    zre
    #
    adantl
    #
    wph
    @101
    @83
    @29
    adantr
    remulcld
    adantlr
    #
    adantr
    @89
    @41
    cr
    wcel
    @83
    @91
    @105
    ad2antrr
    wph
    @82
    @83
    @91
    simpllr
    ltadd2d
    mpbird
    @93
    @5
    @40
    cT
    @83
    @127
    @89
    @91
    @128
    ad2antlr
    @89
    @40
    cr
    wcel
    @83
    @91
    @104
    ad2antrr
    wph
    cT
    crp
    wcel
    @82
    @83
    @91
    wph
    cT
    @29
    @34
    elrpd
    ad3antrrr
    ltmul1d
    mpbird
    @92
    vj
    cv
    #
    cz
    wcel
    #
    wa
    #
    @111
    wa
    #
    @37
    @131
    cT
    cmul
    co
    #
    caddc
    co
    #
    @110
    wcel
    #
    wa
    #
    @5
    @131
    clt
    wbr
    #
    wa
    #
    @131
    @94
    wceq
    #
    wi
    #
    @112
    @113
    wa
    #
    @114
    wa
    #
    @115
    wi
    vj
    @40
    @39
    cfl
    fvex
    @131
    @40
    wceq
    #
    @140
    @144
    @141
    @115
    @145
    @138
    @143
    @139
    @114
    @145
    @134
    @112
    @137
    @113
    @145
    @133
    @109
    @111
    @145
    @132
    @108
    @92
    @131
    @40
    cz
    eleq1
    anbi2d
    anbi1d
    @145
    @136
    @42
    @110
    @145
    @135
    @41
    @37
    caddc
    @131
    @40
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    anbi12d
    @131
    @40
    @5
    clt
    breq2
    anbi12d
    @131
    @40
    @94
    eqeq1
    imbi12d
    @89
    vi
    cv
    #
    cz
    wcel
    #
    wa
    #
    @132
    wa
    #
    @37
    @146
    cT
    cmul
    co
    #
    caddc
    co
    #
    @110
    wcel
    #
    wa
    #
    @137
    wa
    #
    @146
    @131
    clt
    wbr
    #
    wa
    #
    @131
    @146
    c1
    caddc
    co
    #
    wceq
    #
    wi
    @142
    vi
    vk
    @146
    @5
    wceq
    #
    @156
    @140
    @158
    @141
    @159
    @154
    @138
    @155
    @139
    @159
    @153
    @134
    @137
    @159
    @149
    @133
    @152
    @111
    @159
    @148
    @92
    @132
    @159
    @147
    @83
    @89
    @146
    @5
    cz
    eleq1
    anbi2d
    anbi1d
    @159
    @151
    @74
    @110
    @159
    @150
    @6
    @37
    caddc
    @146
    @5
    cT
    cmul
    oveq1
    oveq2d
    eleq1d
    anbi12d
    anbi1d
    @146
    @5
    @131
    clt
    breq1
    anbi12d
    @159
    @157
    @94
    @131
    @146
    @5
    c1
    caddc
    oveq1
    eqeq2d
    imbi12d
    @156
    cA
    cB
    cT
    @146
    @131
    @37
    @156
    wph
    cA
    cr
    wcel
    #
    wph
    @82
    @147
    @132
    @152
    @137
    @155
    simp-6l
    #
    fourierdlem51.a
    syl
    @156
    wph
    @99
    @161
    fourierdlem51.b
    syl
    @156
    wph
    @30
    @161
    @31
    syl
    fourierdlem51.t
    wph
    @82
    @147
    @132
    @152
    @137
    @155
    simp-6r
    @89
    @147
    @132
    @152
    @137
    @155
    simp-5r
    @148
    @132
    @152
    @137
    @155
    simp-4r
    @154
    @155
    simpr
    @149
    @152
    @137
    @155
    simpllr
    @153
    @137
    @155
    simplr
    fourierdlem6
    chvarv
    vtocl
    syl21anc
    oveq1d
    oveq2d
    @93
    @96
    @37
    @6
    cT
    caddc
    co
    #
    caddc
    co
    #
    @74
    cT
    caddc
    co
    #
    cB
    @92
    @96
    @163
    wceq
    #
    @91
    wph
    @83
    @165
    @82
    @126
    @95
    @162
    @37
    caddc
    @126
    @5
    cT
    @126
    @5
    @129
    recnd
    wph
    cT
    cc
    wcel
    #
    @83
    wph
    cT
    @29
    recnd
    #
    adantr
    adddirp1d
    oveq2d
    adantlr
    adantr
    @92
    @163
    @164
    wceq
    @91
    @92
    @164
    @163
    @92
    @37
    @6
    cT
    @89
    @37
    cc
    wcel
    @83
    @89
    @37
    @98
    recnd
    adantr
    @92
    @6
    @130
    recnd
    wph
    @166
    @82
    @83
    @167
    ad2antrr
    addassd
    eqcomd
    adantr
    @93
    @164
    cA
    cT
    caddc
    co
    #
    cB
    @91
    @164
    @168
    wceq
    @92
    @74
    cA
    cT
    caddc
    oveq1
    adantl
    wph
    @168
    cB
    wceq
    #
    @82
    @83
    @91
    wph
    @32
    @169
    @33
    wph
    cB
    cA
    cT
    wph
    cB
    fourierdlem51.b
    recnd
    wph
    cA
    fourierdlem51.a
    recnd
    @167
    subaddd
    mpbid
    ad3antrrr
    eqtrd
    3eqtrd
    3eqtrd
    wph
    cB
    cC
    wcel
    @82
    @83
    @91
    fourierdlem51.bc
    ad3antrrr
    eqeltrd
    3adantl3
    @90
    @91
    wn
    #
    wa
    #
    @73
    @74
    cC
    @171
    @89
    @83
    @74
    @120
    wcel
    #
    @73
    @74
    wceq
    @89
    @83
    @75
    @170
    simpl1
    #
    @89
    @83
    @75
    @170
    simpl2
    #
    @171
    @172
    @111
    @74
    cA
    wne
    #
    @90
    @111
    @170
    @89
    @75
    @111
    @83
    wph
    @75
    @111
    @82
    wph
    cC
    @110
    @74
    fourierdlem51.css
    sselda
    adantlr
    3adant2
    adantr
    @170
    @175
    @90
    @74
    cA
    neqne
    adantl
    @171
    cA
    cB
    @74
    @171
    @89
    @160
    @173
    wph
    @160
    @82
    fourierdlem51.a
    adantr
    syl
    @171
    @89
    @99
    @173
    @100
    syl
    @171
    @89
    @83
    @74
    cxr
    wcel
    @173
    @174
    @92
    @74
    @92
    @37
    @6
    wph
    @82
    @83
    simplr
    @130
    readdcld
    rexrd
    syl2anc
    eliccelioc
    mpbir2and
    @92
    @172
    wa
    #
    @73
    @42
    @74
    @89
    @97
    @83
    @172
    @106
    ad2antrr
    @176
    @41
    @6
    @37
    caddc
    @176
    @40
    @5
    cT
    cmul
    @176
    cA
    cB
    cT
    @40
    @5
    @37
    wph
    @160
    @82
    @83
    @172
    fourierdlem51.a
    ad3antrrr
    wph
    @99
    @82
    @83
    @172
    fourierdlem51.b
    ad3antrrr
    wph
    @30
    @82
    @83
    @172
    @31
    ad3antrrr
    fourierdlem51.t
    wph
    @82
    @83
    @172
    simpllr
    @89
    @108
    @83
    @172
    @103
    ad2antrr
    @89
    @83
    @172
    simplr
    @89
    @42
    @120
    wcel
    @83
    @172
    @89
    @73
    @42
    @120
    @106
    @122
    eqeltrrd
    ad2antrr
    @92
    @172
    simpr
    fourierdlem35
    oveq1d
    oveq2d
    eqtrd
    syl21anc
    @89
    @83
    @75
    @170
    simpl3
    eqeltrd
    pm2.61dan
    3exp
    syl2anc
    rexlimd
    mpd
    eqeltrd
    @70
    eqid
    fmptd
    wph
    @53
    cC
    @58
    @70
    wph
    vx
    @53
    cr
    @58
    wph
    cr
    cr
    @53
    cE
    wph
    cr
    @120
    cr
    cE
    @121
    wph
    @117
    @99
    @120
    cr
    wss
    @119
    fourierdlem51.b
    cA
    cB
    iocssre
    syl2anc
    fssd
    wph
    @53
    @52
    cr
    @9
    vy
    @52
    ssrab2
    @88
    syl5ss
    #
    fssresd
    feqmptd
    feq1d
    mpbird
    wph
    @68
    vw
    @53
    wph
    @61
    @53
    wcel
    #
    wa
    #
    @67
    vz
    @53
    @179
    @63
    @53
    wcel
    #
    wa
    #
    @65
    @66
    @181
    @65
    wa
    #
    wph
    @61
    cH
    wcel
    #
    wa
    #
    @63
    cH
    wcel
    #
    @63
    cE
    cfv
    #
    @61
    cE
    cfv
    #
    wceq
    #
    @66
    @182
    wph
    @183
    wph
    @178
    @180
    @65
    simplll
    @178
    @183
    wph
    @180
    @65
    @178
    @61
    @53
    cH
    @178
    id
    fourierdlem51.h
    syl6eleqr
    ad3antlr
    jca
    @180
    @185
    @179
    @65
    @180
    @63
    @53
    cH
    @180
    id
    fourierdlem51.h
    syl6eleqr
    ad2antlr
    @182
    @186
    @64
    @62
    @187
    @180
    @186
    @64
    wceq
    @179
    @65
    @180
    @64
    @186
    @63
    @53
    cE
    fvres
    eqcomd
    ad2antlr
    @65
    @64
    @62
    wceq
    @181
    @65
    @62
    @64
    @65
    id
    eqcomd
    adantl
    @178
    @62
    @187
    wceq
    wph
    @180
    @65
    @61
    @53
    cE
    fvres
    ad3antlr
    3eqtrd
    @184
    @185
    wa
    #
    @188
    wa
    #
    @66
    @61
    @63
    clt
    wbr
    wn
    @63
    @61
    clt
    wbr
    wn
    @190
    vx
    vy
    cA
    cB
    cC
    cH
    cT
    vk
    cE
    @61
    cX
    @63
    wph
    @160
    @183
    @185
    @188
    fourierdlem51.a
    ad3antrrr
    #
    wph
    @99
    @183
    @185
    @188
    fourierdlem51.b
    ad3antrrr
    #
    wph
    @30
    @183
    @185
    @188
    @31
    ad3antrrr
    #
    wph
    cX
    cr
    wcel
    @183
    @185
    @188
    fourierdlem51.x
    ad3antrrr
    #
    fourierdlem51.h
    fourierdlem51.t
    fourierdlem51.e
    wph
    @183
    @185
    @188
    simpllr
    #
    @184
    @185
    @188
    simplr
    #
    @189
    @188
    simpr
    #
    fourierdlem19
    @190
    vx
    vy
    cA
    cB
    cC
    cH
    cT
    vk
    cE
    @63
    cX
    @61
    @191
    @192
    @193
    @194
    fourierdlem51.h
    fourierdlem51.t
    fourierdlem51.e
    @196
    @195
    @190
    @186
    @187
    @197
    eqcomd
    fourierdlem19
    @190
    @61
    @63
    @184
    @61
    cr
    wcel
    @185
    @188
    wph
    cH
    cr
    @61
    wph
    cH
    @53
    cr
    fourierdlem51.h
    @177
    syl5eqss
    #
    sselda
    ad2antrr
    @189
    @63
    cr
    wcel
    @188
    @184
    cH
    cr
    @63
    wph
    cH
    cr
    wss
    @183
    @198
    adantr
    sselda
    adantr
    lttri3d
    mpbir2and
    syl21anc
    ex
    ralrimiva
    ralrimiva
    vw
    vz
    @53
    cC
    @58
    dff13
    sylanbrc
    @53
    cC
    @58
    f1fi
    syl2anc
    @51
    @53
    unfi
    sylancr
    wph
    @37
    @54
    wcel
    #
    vx
    @11
    wral
    @56
    wph
    @199
    vx
    @11
    wph
    @37
    @11
    wcel
    #
    wa
    wph
    @37
    @10
    wcel
    #
    @76
    @199
    wph
    @200
    simpl
    @200
    @201
    wph
    @9
    vy
    @37
    @10
    elrabi
    adantl
    @200
    @76
    wph
    @200
    @201
    @76
    @9
    @76
    vy
    @37
    @10
    @80
    elrab
    simprbi
    adantl
    wph
    @201
    wa
    #
    @76
    wa
    #
    @37
    @1
    wceq
    #
    @199
    @204
    @199
    @203
    @204
    @37
    @51
    wcel
    @199
    vx
    @1
    velsn
    @37
    @51
    @53
    elun1
    sylbir
    adantl
    @203
    @204
    wn
    #
    wa
    #
    @71
    @199
    @206
    @78
    @76
    @71
    @202
    @205
    @78
    @76
    @202
    @205
    wa
    #
    @1
    @2
    @37
    wph
    @85
    @201
    @205
    @87
    ad2antrr
    wph
    @2
    cxr
    wcel
    #
    @201
    @205
    wph
    @2
    @18
    rexrd
    #
    ad2antrr
    @202
    @37
    cxr
    wcel
    @205
    @202
    @37
    wph
    @10
    cr
    @37
    wph
    @1
    @2
    @17
    @18
    iccssred
    #
    sselda
    #
    rexrd
    adantr
    @207
    @1
    @37
    wph
    @1
    cr
    wcel
    #
    @201
    @205
    @17
    ad2antrr
    @202
    @82
    @205
    @211
    adantr
    @202
    @1
    @37
    cle
    wbr
    #
    @205
    @202
    @85
    @208
    @201
    @213
    wph
    @85
    @201
    @87
    adantr
    #
    wph
    @208
    @201
    @209
    adantr
    #
    wph
    @201
    simpr
    #
    @1
    @2
    @37
    iccgelb
    syl3anc
    adantr
    @205
    @37
    @1
    wne
    @202
    @37
    @1
    neqne
    adantl
    leneltd
    @202
    @37
    @2
    cle
    wbr
    #
    @205
    @202
    @85
    @208
    @201
    @217
    @214
    @215
    @216
    @1
    @2
    @37
    iccleub
    syl3anc
    adantr
    eliocd
    adantlr
    @202
    @76
    @205
    simplr
    @81
    sylanbrc
    @37
    @53
    @51
    elun2
    syl
    pm2.61dan
    syl21anc
    ralrimiva
    vx
    @11
    @54
    dfss3
    sylibr
    @54
    @11
    ssfi
    syl2anc
    @3
    @11
    unfi
    sylancr
    syl5eqel
    wph
    cD
    @12
    cr
    fourierdlem51.d
    wph
    @3
    @11
    cr
    wph
    @212
    @86
    @3
    cr
    wss
    @17
    @18
    @1
    @2
    cr
    prssi
    syl2anc
    wph
    @11
    @10
    cr
    @9
    vy
    @10
    ssrab2
    @210
    syl5ss
    unssd
    syl5eqss
    fourierdlem51.f
    @46
    eqid
    fourierdlem36
    @48
    @47
    cD
    cF
    wf1o
    @49
    @47
    cD
    clt
    clt
    cF
    isof1o
    @47
    cD
    cF
    f1ofo
    syl
    @47
    cD
    cF
    forn
    3syl
    eleqtrrd
end
