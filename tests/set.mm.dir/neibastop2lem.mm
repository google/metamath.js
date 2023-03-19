include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cpw.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wb.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "weq.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "com.mm"
include "wi.mm"
include "wfn.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "csn.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "wex.mm"
include "n0.mm"
include "inss1.mm"
include "sseli.mm"
include "anassrs.mm"
include "sylan2.mm"
include "adantrl.mm"
include "simprl.mm"
include "wel.mm"
include "fvssunirn.mm"
include "cdif.mm"
include "wf.mm"
include "frn.mm"
include "difss2d.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "syl5ss.mm"
include "sselda.mm"
include "elpwid.mm"
include "adantrr.mm"
include "csuc.mm"
include "simprlr.mm"
include "rspe.mm"
include "ad2ant2l.mm"
include "eliun.mm"
include "pweq.mm"
include "ineq2d.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "wceq.mm"
include "simpll.mm"
include "simprll.mm"
include "fveq1i.mm"
include "snex.mm"
include "fr0g.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "pwidg.mm"
include "snssd.mm"
include "adantr.mm"
include "pwexg.mm"
include "inss2.mm"
include "elpwi.mm"
include "adantl.mm"
include "sspwb.mm"
include "ralrimivw.mm"
include "iunss.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "mpan9.mm"
include "ssexd.mm"
include "iuneq1.mm"
include "frsucmpt2.mm"
include "eqsstrd.mm"
include "expr.mm"
include "expcom.mm"
include "finds2.mm"
include "fvex.mm"
include "elpw.mm"
include "syl6ibr.mm"
include "com12.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "mpbiran.mm"
include "syl12anc.mm"
include "eleqtrrd.mm"
include "peano2.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "elunii.mm"
include "simprr.mm"
include "rabeq2i.mm"
include "sylanbrc.mm"
include "ralimdva.mm"
include "impr.mm"
include "dfss3.mm"
include "selpw.mm"
include "inelcm.mm"
include "rexlimddv.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "rexlimdvaa.mm"
include "rexlimdv.mm"
include "expimpd.mm"
include "raleqbi1dv.mm"
include "snidg.mm"
include "peano1.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "sylancl.mm"
include "eluni2.mm"
include "eleq2.mm"
include "rexrn.mm"
include "ffvelrnda.mm"
include "ad3antrrr.mm"
include "sstrd.mm"
include "elin.mm"
include "simprrr.mm"
include "simpllr.mm"
include "simprrl.mm"
include "elequ1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "sseldd.mm"
include "exp32.mm"
include "rexlimdva.mm"
include "3impia.mm"
include "rabssdv.mm"
include "syl5eqss.mm"
include "sseq1.mm"
include "anbi12d.mm"

theorem neibastop2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cS: class S
  let cU: class U
  let vf: setvar f
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cJ: class J
  let cN: class N
  let cV: class V
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vn: setvar n
  let vj: setvar j
  let vs: setvar s
  let vb: setvar b
  let vg: setvar g
  assume neibastop1.1: |- ( ph -> X e. V )
  assume neibastop1.2: |- ( ph -> F : X --> ( ~P ~P X \ { (/) } ) )
  assume neibastop1.3: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) /\ w e. ( F ` x ) ) ) -> ( ( F ` x ) i^i ~P ( v i^i w ) ) =/= (/) )
  assume neibastop1.4: |- J = { o e. ~P X | A. x e. o ( ( F ` x ) i^i ~P o ) =/= (/) }
  assume neibastop1.5: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> x e. v )
  assume neibastop1.6: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> E. t e. ( F ` x ) A. y e. t ( ( F ` y ) i^i ~P v ) =/= (/) )
  assume neibastop2.p: |- ( ph -> P e. X )
  assume neibastop2.n: |- ( ph -> N C_ X )
  assume neibastop2.f: |- ( ph -> U e. ( F ` P ) )
  assume neibastop2.u: |- ( ph -> U C_ N )
  assume neibastop2.g: |- G = ( rec ( ( a e. _V |-> U_ z e. a U_ x e. X ( ( F ` x ) i^i ~P z ) ) , { U } ) |` _om )
  assume neibastop2.s: |- S = { y e. X | E. f e. U. ran G ( ( F ` y ) i^i ~P f ) =/= (/) }

  disjoint f t
  disjoint f v
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint t v
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v x
  disjoint J v
  disjoint x y
  disjoint x z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint f o
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint P f
  disjoint o t
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint P o
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint P t
  disjoint u w
  disjoint P u
  disjoint v w
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint N f
  disjoint N o
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint S f
  disjoint S o
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint U f
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint a f
  disjoint a o
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint F f
  disjoint F o
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint f ph
  disjoint o ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X a
  disjoint X f
  disjoint X o
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint k t
  disjoint k v
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n t
  disjoint n v
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint j n
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint n s
  disjoint n u
  disjoint n x
  disjoint J n
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint J s
  disjoint f s
  disjoint o s
  disjoint s t
  disjoint s w
  disjoint P s
  disjoint k o
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint N k
  disjoint N s
  disjoint S k
  disjoint U k
  disjoint U n
  disjoint a b
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint b f
  disjoint b g
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b o
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint f g
  disjoint f j
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g o
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j o
  disjoint j t
  disjoint j w
  disjoint F j
  disjoint F k
  disjoint n o
  disjoint n w
  disjoint F n
  disjoint F s
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint X b
  disjoint X g
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X s
  assert |- ( ph -> E. u e. J ( P e. u /\ u C_ N ) )

  proof
    wph
    cS
    cJ
    wcel
    #
    cP
    cS
    wcel
    #
    cS
    cN
    wss
    #
    cP
    vu
    cv
    #
    wcel
    #
    @3
    cN
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    wph
    cS
    cX
    cpw
    #
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    #
    cS
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    cS
    wral
    #
    @0
    wph
    @8
    cS
    cX
    wss
    #
    cS
    vy
    cv
    #
    cF
    cfv
    #
    vf
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vf
    cG
    crn
    #
    cuni
    #
    wrex
    #
    vy
    cX
    crab
    #
    cX
    neibastop2.s
    @24
    vy
    cX
    ssrab2
    eqsstri
    wph
    cX
    cV
    wcel
    @8
    @15
    wb
    neibastop1.1
    cS
    cX
    cV
    elpw2g
    syl
    mpbiri
    wph
    @13
    vx
    cS
    @9
    cS
    wcel
    @9
    cX
    wcel
    #
    @10
    @19
    cin
    #
    c0
    wne
    #
    vf
    @23
    wrex
    #
    wa
    wph
    @13
    @24
    @29
    vy
    @9
    cX
    cS
    vy
    vx
    weq
    #
    @21
    @28
    vf
    @23
    @30
    @20
    @27
    c0
    @30
    @17
    @10
    @19
    @16
    @9
    cF
    fveq2
    ineq1d
    neeq1d
    rexbidv
    neibastop2.s
    elrab2
    wph
    @26
    @29
    @13
    wph
    @26
    wa
    #
    @28
    @13
    vf
    @23
    @18
    @23
    wcel
    #
    @18
    vk
    cv
    #
    cG
    cfv
    #
    wcel
    #
    vk
    com
    wrex
    #
    @31
    @28
    @13
    wi
    #
    cG
    com
    wfn
    #
    @32
    @36
    wb
    @38
    va
    cvv
    vz
    va
    cv
    #
    vx
    cX
    @10
    vz
    cv
    #
    cpw
    #
    cin
    #
    ciun
    #
    ciun
    #
    cmpt
    #
    cU
    csn
    #
    crdg
    com
    cres
    #
    com
    wfn
    @46
    @45
    frfnom
    com
    cG
    @47
    neibastop2.g
    fneq1i
    mpbir
    #
    vk
    @18
    cG
    com
    fnunirn
    ax-mp
    @31
    @35
    @37
    vk
    com
    @28
    vv
    cv
    #
    @27
    wcel
    #
    vv
    wex
    @31
    @33
    com
    wcel
    #
    @35
    wa
    #
    wa
    #
    @13
    vv
    @27
    n0
    @53
    @50
    @13
    vv
    @31
    @52
    @50
    @13
    @31
    @52
    @50
    wa
    #
    wa
    #
    @17
    @49
    cpw
    #
    cin
    #
    c0
    wne
    #
    vy
    vt
    cv
    #
    wral
    #
    @13
    vt
    @10
    @31
    @50
    @60
    vt
    @10
    wrex
    #
    @52
    @50
    @31
    @49
    @10
    wcel
    #
    @61
    @27
    @10
    @49
    @10
    @19
    inss1
    sseli
    wph
    @26
    @62
    @61
    neibastop1.6
    anassrs
    sylan2
    adantrl
    @55
    @59
    @10
    wcel
    #
    @60
    wa
    wa
    #
    @63
    @59
    @11
    wcel
    #
    @13
    @55
    @63
    @60
    simprl
    @64
    @59
    cS
    wss
    #
    @65
    @64
    @16
    cS
    wcel
    #
    vy
    @59
    wral
    #
    @66
    @55
    @63
    @60
    @68
    @55
    @63
    wa
    #
    @58
    @67
    vy
    @59
    @69
    vy
    vt
    wel
    #
    @58
    @67
    @69
    @70
    @58
    wa
    #
    wa
    #
    @16
    cX
    wcel
    #
    @24
    @67
    @69
    @70
    @73
    @58
    @69
    @59
    cX
    @16
    @69
    @59
    cX
    @55
    @10
    @7
    @59
    @55
    @10
    cF
    crn
    #
    cuni
    #
    @7
    cF
    @9
    fvssunirn
    wph
    @75
    @7
    wss
    #
    @26
    @54
    wph
    @74
    @7
    cpw
    #
    wss
    @76
    wph
    @74
    @77
    c0
    csn
    #
    wph
    cX
    @77
    @78
    cdif
    #
    cF
    wf
    @74
    @79
    wss
    neibastop1.2
    cX
    @79
    cF
    frn
    syl
    difss2d
    @74
    @7
    sspwuni
    sylib
    ad2antrr
    syl5ss
    sselda
    elpwid
    sselda
    adantrr
    @72
    @49
    @23
    wcel
    #
    @58
    @24
    @55
    @80
    @63
    @71
    @55
    @49
    @33
    csuc
    #
    cG
    cfv
    #
    wcel
    @82
    @22
    wcel
    #
    @80
    @55
    @49
    vz
    @34
    @43
    ciun
    #
    @82
    @55
    @49
    @43
    wcel
    #
    vz
    @34
    wrex
    #
    @49
    @84
    wcel
    @55
    @35
    @50
    vx
    cX
    wrex
    #
    @86
    @31
    @51
    @35
    @50
    simprlr
    @26
    @50
    @87
    wph
    @52
    @50
    vx
    cX
    rspe
    ad2ant2l
    @85
    @87
    vz
    @18
    @34
    @85
    @49
    @42
    wcel
    #
    vx
    cX
    wrex
    vz
    vf
    weq
    #
    @87
    vx
    @49
    cX
    @42
    eliun
    @89
    @88
    @50
    vx
    cX
    @89
    @42
    @27
    @49
    @89
    @41
    @19
    @10
    @40
    @18
    pweq
    ineq2d
    eleq2d
    rexbidv
    syl5bb
    rspcev
    syl2anc
    vz
    @49
    @34
    @43
    eliun
    sylibr
    @55
    wph
    @51
    @34
    cU
    cpw
    #
    wss
    #
    @82
    @84
    wceq
    #
    wph
    @26
    @54
    simpll
    @31
    @51
    @35
    @50
    simprll
    #
    @55
    @34
    @23
    @90
    cG
    @33
    fvssunirn
    wph
    @23
    @90
    wss
    #
    @26
    @54
    wph
    @22
    @90
    cpw
    #
    wss
    #
    @94
    wph
    com
    @95
    cG
    wf
    #
    @96
    wph
    vn
    cv
    #
    cG
    cfv
    #
    @95
    wcel
    #
    vn
    com
    wral
    #
    @97
    wph
    @100
    vn
    com
    @98
    com
    wcel
    #
    wph
    @100
    @102
    wph
    @99
    @90
    wss
    #
    @100
    @103
    @46
    @90
    wss
    @91
    @82
    @90
    wss
    #
    wph
    vn
    vk
    @98
    c0
    wceq
    #
    @99
    @46
    @90
    @105
    @99
    c0
    cG
    cfv
    #
    @46
    @98
    c0
    cG
    fveq2
    @106
    c0
    @47
    cfv
    #
    @46
    c0
    cG
    @47
    neibastop2.g
    fveq1i
    @46
    cvv
    wcel
    @107
    @46
    wceq
    cU
    snex
    @46
    cvv
    @45
    fr0g
    ax-mp
    eqtri
    #
    syl6eq
    sseq1d
    vn
    vk
    weq
    @99
    @34
    @90
    @98
    @33
    cG
    fveq2
    sseq1d
    @98
    @81
    wceq
    @99
    @82
    @90
    @98
    @81
    cG
    fveq2
    sseq1d
    wph
    cU
    @90
    wph
    cU
    cP
    cF
    cfv
    #
    wcel
    #
    cU
    @90
    wcel
    #
    neibastop2.f
    cU
    @109
    pwidg
    syl
    #
    snssd
    wph
    @51
    @91
    @104
    wi
    wph
    @51
    @91
    @104
    wph
    @51
    @91
    wa
    #
    wa
    #
    @82
    @84
    @90
    @114
    @51
    @84
    cvv
    wcel
    @92
    wph
    @51
    @91
    simprl
    @114
    @84
    @90
    cvv
    @114
    @110
    @90
    cvv
    wcel
    wph
    @110
    @113
    neibastop2.f
    adantr
    cU
    @109
    pwexg
    syl
    @114
    @43
    @90
    wss
    #
    vz
    @34
    wral
    #
    @84
    @90
    wss
    wph
    @115
    vz
    @90
    wral
    #
    @113
    @116
    wph
    @115
    vz
    @90
    wph
    @40
    @90
    wcel
    #
    wa
    #
    @42
    @90
    wss
    #
    vx
    cX
    wral
    @115
    @119
    @120
    vx
    cX
    @119
    @42
    @41
    @90
    @10
    @41
    inss2
    @119
    @40
    cU
    wss
    #
    @41
    @90
    wss
    @118
    @121
    wph
    @40
    cU
    elpwi
    adantl
    @40
    cU
    sspwb
    sylib
    syl5ss
    ralrimivw
    vx
    cX
    @42
    @90
    iunss
    sylibr
    ralrimiva
    @91
    @117
    @116
    wi
    @51
    @115
    vz
    @34
    @90
    ssralv
    adantl
    mpan9
    vz
    @34
    @43
    @90
    iunss
    sylibr
    #
    ssexd
    va
    vy
    @46
    @33
    @44
    @84
    vz
    @16
    @43
    ciun
    cG
    cvv
    neibastop2.g
    vz
    @16
    @39
    @43
    iuneq1
    vz
    @16
    @34
    @43
    iuneq1
    frsucmpt2
    syl2anc
    #
    @122
    eqsstrd
    expr
    expcom
    finds2
    @99
    @90
    @98
    cG
    fvex
    elpw
    syl6ibr
    com12
    ralrimiv
    @97
    @38
    @101
    @48
    vn
    com
    @95
    cG
    ffnfv
    mpbiran
    sylibr
    #
    com
    @95
    cG
    frn
    syl
    @22
    @90
    sspwuni
    sylib
    ad2antrr
    syl5ss
    @123
    syl12anc
    eleqtrrd
    @55
    @38
    @81
    com
    wcel
    #
    @83
    @48
    @55
    @51
    @125
    @93
    @33
    peano2
    syl
    com
    @81
    cG
    fnfvelrn
    sylancr
    @49
    @82
    @22
    elunii
    syl2anc
    ad2antrr
    @69
    @70
    @58
    simprr
    @21
    @58
    vf
    @49
    @23
    vf
    vv
    weq
    #
    @20
    @57
    c0
    @126
    @19
    @56
    @17
    @18
    @49
    pweq
    ineq2d
    neeq1d
    rspcev
    syl2anc
    @24
    vy
    cS
    cX
    neibastop2.s
    rabeq2i
    sylanbrc
    expr
    ralimdva
    impr
    vy
    @59
    cS
    dfss3
    sylibr
    vt
    cS
    selpw
    sylibr
    @59
    @10
    @11
    inelcm
    syl2anc
    rexlimddv
    expr
    exlimdv
    syl5bi
    rexlimdvaa
    syl5bi
    rexlimdv
    expimpd
    syl5bi
    ralrimiv
    @10
    vo
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @127
    wral
    @14
    vo
    cS
    @7
    cJ
    @130
    @13
    vx
    @127
    cS
    @127
    cS
    wceq
    #
    @129
    @12
    c0
    @131
    @128
    @11
    @10
    @127
    cS
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    sylanbrc
    wph
    cP
    cX
    wcel
    @109
    @19
    cin
    #
    c0
    wne
    #
    vf
    @23
    wrex
    #
    @1
    neibastop2.p
    wph
    cU
    @23
    wcel
    #
    @109
    @90
    cin
    #
    c0
    wne
    #
    @134
    wph
    cU
    @46
    wcel
    #
    @46
    @22
    wcel
    @135
    wph
    @110
    @138
    neibastop2.f
    cU
    @109
    snidg
    syl
    @106
    @46
    @22
    @108
    @38
    c0
    com
    wcel
    @106
    @22
    wcel
    @48
    peano1
    com
    c0
    cG
    fnfvelrn
    mp2an
    eqeltrri
    cU
    @46
    @22
    elunii
    sylancl
    wph
    @110
    @111
    @137
    neibastop2.f
    @112
    cU
    @109
    @90
    inelcm
    syl2anc
    @133
    @137
    vf
    cU
    @23
    @18
    cU
    wceq
    #
    @132
    @136
    c0
    @139
    @19
    @90
    @109
    @18
    cU
    pweq
    ineq2d
    neeq1d
    rspcev
    syl2anc
    @24
    @134
    vy
    cP
    cX
    cS
    @16
    cP
    wceq
    #
    @21
    @133
    vf
    @23
    @140
    @20
    @132
    c0
    @140
    @17
    @109
    @19
    @16
    cP
    cF
    fveq2
    ineq1d
    neeq1d
    rexbidv
    neibastop2.s
    elrab2
    sylanbrc
    wph
    cS
    @25
    cN
    neibastop2.s
    wph
    @24
    vy
    cX
    cN
    wph
    @73
    @24
    @16
    cN
    wcel
    #
    wph
    @73
    wa
    #
    @21
    @141
    vf
    @23
    @32
    vf
    vz
    wel
    #
    vz
    @22
    wrex
    #
    @142
    @21
    @141
    wi
    #
    vz
    @18
    @22
    eluni2
    @144
    @36
    @142
    @145
    @38
    @144
    @36
    wb
    @48
    @143
    @35
    vz
    vk
    com
    cG
    @40
    @34
    @18
    eleq2
    rexrn
    ax-mp
    @142
    @35
    @145
    vk
    com
    @142
    @51
    wa
    #
    @35
    @21
    @141
    @146
    @35
    @21
    wa
    #
    wa
    #
    @18
    cN
    @16
    @148
    @18
    cU
    cN
    @148
    @18
    cU
    @146
    @35
    @18
    @90
    wcel
    @21
    @146
    @34
    @90
    @18
    @146
    @34
    @90
    @142
    com
    @95
    @33
    cG
    wph
    @97
    @73
    @124
    adantr
    ffvelrnda
    elpwid
    sselda
    adantrr
    elpwid
    wph
    cU
    cN
    wss
    @73
    @51
    @147
    neibastop2.u
    ad3antrrr
    sstrd
    @146
    @35
    @21
    vy
    vf
    wel
    #
    @21
    @49
    @20
    wcel
    #
    vv
    wex
    @146
    @35
    wa
    #
    @149
    vv
    @20
    n0
    @151
    @150
    @149
    vv
    @150
    @49
    @17
    wcel
    #
    @49
    @19
    wcel
    #
    wa
    #
    @151
    @149
    @49
    @17
    @19
    elin
    @146
    @35
    @154
    @149
    @146
    @35
    @154
    wa
    #
    wa
    #
    @49
    @18
    @16
    @156
    @49
    @18
    @146
    @35
    @152
    @153
    simprrr
    elpwid
    @156
    @73
    @62
    vx
    vv
    wel
    #
    wi
    #
    vx
    cX
    wral
    #
    @152
    vy
    vv
    wel
    #
    wph
    @73
    @51
    @155
    simpllr
    wph
    @159
    @73
    @51
    @155
    wph
    @158
    vx
    cX
    wph
    @26
    @62
    @157
    neibastop1.5
    expr
    ralrimiva
    ad3antrrr
    @146
    @35
    @152
    @153
    simprrl
    @158
    @152
    @160
    wi
    vx
    @16
    cX
    vx
    vy
    weq
    #
    @62
    @152
    @157
    @160
    @161
    @10
    @17
    @49
    @9
    @16
    cF
    fveq2
    eleq2d
    vx
    vy
    vv
    elequ1
    imbi12d
    rspcv
    syl3c
    sseldd
    expr
    syl5bi
    exlimdv
    syl5bi
    impr
    sseldd
    exp32
    rexlimdva
    syl5bi
    syl5bi
    rexlimdv
    3impia
    rabssdv
    syl5eqss
    @6
    @1
    @2
    wa
    vu
    cS
    cJ
    @3
    cS
    wceq
    @4
    @1
    @5
    @2
    @3
    cS
    cP
    eleq2
    @3
    cS
    cN
    sseq1
    anbi12d
    rspcev
    syl12anc
end
