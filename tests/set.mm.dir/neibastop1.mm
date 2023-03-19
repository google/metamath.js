include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wrex.mm"
include "eluni2.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "sspwb.mm"
include "sslin.mm"
include "syl.mm"
include "sselda.mm"
include "adantrr.mm"
include "weq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "raleqbi1dv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "simprr.mm"
include "rsp.mm"
include "sylc.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "sylanbrc.mm"
include "ex.mm"
include "alrimiv.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "inss1.mm"
include "elpwi.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "inss2.mm"
include "anim12i.mm"
include "r19.26.mm"
include "wex.mm"
include "n0.mm"
include "eeanv.mm"
include "simprl.mm"
include "sseldi.mm"
include "elpwid.mm"
include "ss2in.mm"
include "simplll.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "syl13anc.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "ralimdva.mm"
include "syl5.mm"
include "impr.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wb.mm"
include "mpbi.mm"
include "a1i.mm"
include "ssexd.mm"
include "uniexb.mm"
include "istopg.mm"
include "mpbir2and.mm"
include "pwidg.mm"
include "csn.mm"
include "cdif.mm"
include "ffvelrnda.mm"
include "eldifi.mm"
include "3syl.mm"
include "df-ss.mm"
include "eldifsni.mm"
include "eqnetrd.mm"
include "ralrimiva.mm"
include "eqssd.mm"
include "istopon.mm"

theorem neibastop1
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let cP: class P
  let cN: class N
  let cS: class S
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume neibastop1.1: |- ( ph -> X e. V )
  assume neibastop1.2: |- ( ph -> F : X --> ( ~P ~P X \ { (/) } ) )
  assume neibastop1.3: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) /\ w e. ( F ` x ) ) ) -> ( ( F ` x ) i^i ~P ( v i^i w ) ) =/= (/) )
  assume neibastop1.4: |- J = { o e. ~P X | A. x e. o ( ( F ` x ) i^i ~P o ) =/= (/) }

  disjoint v x
  disjoint J v
  disjoint J x
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint v w
  disjoint w x
  disjoint F o
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint o ph
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint X o
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint f k
  disjoint f n
  disjoint f t
  disjoint f v
  disjoint f y
  disjoint f z
  disjoint G f
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
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint x y
  disjoint x z
  disjoint J y
  disjoint J z
  disjoint f o
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint P f
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o y
  disjoint o z
  disjoint P o
  disjoint s t
  disjoint s w
  disjoint P s
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint P t
  disjoint u w
  disjoint P u
  disjoint P v
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint N f
  disjoint k o
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint N k
  disjoint N o
  disjoint N s
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint S f
  disjoint S k
  disjoint S o
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint U f
  disjoint U k
  disjoint U n
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a o
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
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
  disjoint F f
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
  disjoint F t
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph y
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X g
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X y
  disjoint X z
  assert |- ( ph -> J e. ( TopOn ` X ) )

  proof
    wph
    cJ
    ctop
    wcel
    #
    cX
    cJ
    cuni
    #
    wceq
    cJ
    cX
    ctopon
    cfv
    wcel
    wph
    @0
    vy
    cv
    #
    cJ
    wss
    #
    @2
    cuni
    #
    cJ
    wcel
    #
    wi
    #
    vy
    wal
    #
    @2
    vz
    cv
    #
    cin
    #
    cJ
    wcel
    #
    vz
    cJ
    wral
    vy
    cJ
    wral
    #
    wph
    @6
    vy
    wph
    @3
    @5
    wph
    @3
    wa
    #
    @4
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
    @4
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @4
    wral
    #
    @5
    @12
    @4
    cX
    wss
    #
    @14
    @12
    @2
    @13
    wss
    @21
    @12
    @2
    cJ
    @13
    wph
    @3
    simpr
    #
    cJ
    @16
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
    @23
    wral
    #
    vo
    @13
    crab
    @13
    neibastop1.4
    @27
    vo
    @13
    ssrab2
    eqsstri
    #
    syl6ss
    @2
    cX
    sspwuni
    sylib
    @4
    cX
    vy
    vuniex
    elpw
    sylibr
    @12
    @19
    vx
    @4
    @15
    @4
    wcel
    @15
    @8
    wcel
    #
    vz
    @2
    wrex
    @12
    @19
    vz
    @15
    @2
    eluni2
    @12
    @29
    @19
    vz
    @2
    @12
    @8
    @2
    wcel
    #
    @29
    wa
    wa
    #
    @16
    @8
    cpw
    #
    cin
    #
    @18
    wss
    #
    @33
    c0
    wne
    #
    @19
    @31
    @32
    @17
    wss
    #
    @34
    @31
    @8
    @4
    wss
    #
    @36
    @30
    @37
    @12
    @29
    @8
    @2
    elssuni
    ad2antrl
    @8
    @4
    sspwb
    sylib
    @32
    @17
    @16
    sslin
    syl
    @31
    @35
    vx
    @8
    wral
    #
    @29
    @35
    @31
    @8
    cJ
    wcel
    #
    @38
    @12
    @30
    @39
    @29
    @12
    @2
    cJ
    @8
    @22
    sselda
    adantrr
    @39
    @8
    @13
    wcel
    #
    @38
    @27
    @38
    vo
    @8
    @13
    cJ
    @26
    @35
    vx
    @23
    @8
    vo
    vz
    weq
    #
    @25
    @33
    c0
    @41
    @24
    @32
    @16
    @23
    @8
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    #
    simprbi
    syl
    @12
    @30
    @29
    simprr
    @35
    vx
    @8
    rsp
    sylc
    @33
    @18
    ssn0
    syl2anc
    rexlimdvaa
    syl5bi
    ralrimiv
    @27
    @20
    vo
    @4
    @13
    cJ
    @26
    @19
    vx
    @23
    @4
    @23
    @4
    wceq
    #
    @25
    @18
    c0
    @43
    @24
    @17
    @16
    @23
    @4
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    sylanbrc
    ex
    alrimiv
    wph
    @10
    vy
    vz
    cJ
    cJ
    @2
    cJ
    wcel
    #
    @39
    wa
    #
    wph
    @2
    @13
    wcel
    #
    @40
    wa
    #
    @16
    @2
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @2
    wral
    #
    @38
    wa
    #
    wa
    #
    @10
    @45
    @46
    @51
    wa
    #
    @40
    @38
    wa
    #
    wa
    @53
    @44
    @54
    @39
    @55
    @27
    @51
    vo
    @2
    @13
    cJ
    @26
    @50
    vx
    @23
    @2
    vo
    vy
    weq
    #
    @25
    @49
    c0
    @56
    @24
    @48
    @16
    @23
    @2
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    @42
    anbi12i
    @46
    @51
    @40
    @38
    an4
    bitri
    wph
    @53
    wa
    #
    @9
    @13
    wcel
    #
    @16
    @9
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @9
    wral
    #
    @10
    @57
    @9
    cX
    wss
    #
    @58
    wph
    @47
    @63
    @52
    @46
    @63
    wph
    @40
    @46
    @9
    @2
    cX
    @2
    @8
    inss1
    #
    @2
    cX
    elpwi
    syl5ss
    ad2antrl
    #
    adantrr
    @9
    cX
    @2
    @8
    vy
    vex
    inex1
    elpw
    sylibr
    wph
    @47
    @52
    @62
    @52
    @50
    @35
    wa
    #
    vx
    @9
    wral
    #
    wph
    @47
    wa
    #
    @62
    @52
    @50
    vx
    @9
    wral
    #
    @35
    vx
    @9
    wral
    #
    wa
    @67
    @51
    @69
    @38
    @70
    @9
    @2
    wss
    @51
    @69
    wi
    @64
    @50
    vx
    @9
    @2
    ssralv
    ax-mp
    @9
    @8
    wss
    @38
    @70
    wi
    @2
    @8
    inss2
    @35
    vx
    @9
    @8
    ssralv
    ax-mp
    anim12i
    @50
    @35
    vx
    @9
    r19.26
    sylibr
    @68
    @66
    @61
    vx
    @9
    @66
    vv
    cv
    #
    @49
    wcel
    #
    vv
    wex
    #
    vw
    cv
    #
    @33
    wcel
    #
    vw
    wex
    #
    wa
    #
    @68
    @15
    @9
    wcel
    #
    wa
    #
    @61
    @50
    @73
    @35
    @76
    vv
    @49
    n0
    vw
    @33
    n0
    anbi12i
    @77
    @72
    @75
    wa
    #
    vw
    wex
    vv
    wex
    @79
    @61
    @72
    @75
    vv
    vw
    eeanv
    @79
    @80
    @61
    vv
    vw
    @79
    @80
    @61
    @79
    @80
    wa
    #
    @16
    @71
    @74
    cin
    #
    cpw
    #
    cin
    #
    @60
    wss
    #
    @84
    c0
    wne
    #
    @61
    @81
    @83
    @59
    wss
    #
    @85
    @81
    @82
    @9
    wss
    #
    @87
    @81
    @71
    @2
    wss
    @74
    @8
    wss
    @88
    @81
    @71
    @2
    @81
    @49
    @48
    @71
    @16
    @48
    inss2
    @79
    @72
    @75
    simprl
    #
    sseldi
    elpwid
    @81
    @74
    @8
    @81
    @33
    @32
    @74
    @16
    @32
    inss2
    @79
    @72
    @75
    simprr
    #
    sseldi
    elpwid
    @71
    @2
    @74
    @8
    ss2in
    syl2anc
    @82
    @9
    sspwb
    sylib
    @83
    @59
    @16
    sslin
    syl
    @81
    wph
    @15
    cX
    wcel
    #
    @71
    @16
    wcel
    @74
    @16
    wcel
    @86
    wph
    @47
    @78
    @80
    simplll
    @81
    @9
    cX
    @15
    @68
    @63
    @78
    @80
    @65
    ad2antrr
    @68
    @78
    @80
    simplr
    sseldd
    @81
    @49
    @16
    @71
    @16
    @48
    inss1
    @89
    sseldi
    @81
    @33
    @16
    @74
    @16
    @32
    inss1
    @90
    sseldi
    neibastop1.3
    syl13anc
    @84
    @60
    ssn0
    syl2anc
    ex
    exlimdvv
    syl5bir
    syl5bi
    ralimdva
    syl5
    impr
    @27
    @62
    vo
    @9
    @13
    cJ
    @26
    @61
    vx
    @23
    @9
    @23
    @9
    wceq
    #
    @25
    @60
    c0
    @92
    @24
    @59
    @16
    @23
    @9
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    sylanbrc
    sylan2b
    ralrimivva
    wph
    cJ
    cvv
    wcel
    #
    @0
    @7
    @11
    wa
    wb
    wph
    @1
    cvv
    wcel
    @93
    wph
    @1
    cX
    cV
    neibastop1.1
    @1
    cX
    wss
    #
    wph
    cJ
    @13
    wss
    @94
    @28
    cJ
    cX
    sspwuni
    mpbi
    a1i
    #
    ssexd
    cJ
    uniexb
    sylibr
    vy
    vz
    cvv
    cJ
    istopg
    syl
    mpbir2and
    wph
    cX
    @1
    wph
    cX
    cJ
    wcel
    #
    cX
    @1
    wss
    wph
    cX
    @13
    wcel
    #
    @16
    @13
    cin
    #
    c0
    wne
    #
    vx
    cX
    wral
    #
    @96
    wph
    cX
    cV
    wcel
    @97
    neibastop1.1
    cX
    cV
    pwidg
    syl
    wph
    @99
    vx
    cX
    wph
    @91
    wa
    #
    @98
    @16
    c0
    @101
    @16
    @13
    wss
    #
    @98
    @16
    wceq
    @101
    @16
    @13
    cpw
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    @16
    @103
    wcel
    @102
    wph
    cX
    @105
    @15
    cF
    neibastop1.2
    ffvelrnda
    #
    @16
    @103
    @104
    eldifi
    @16
    @13
    elpwi
    3syl
    @16
    @13
    df-ss
    sylib
    @101
    @106
    @16
    c0
    wne
    @107
    @16
    @103
    c0
    eldifsni
    syl
    eqnetrd
    ralrimiva
    @27
    @100
    vo
    cX
    @13
    cJ
    @26
    @99
    vx
    @23
    cX
    @23
    cX
    wceq
    #
    @25
    @98
    c0
    @108
    @24
    @13
    @16
    @23
    cX
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    sylanbrc
    cX
    cJ
    elssuni
    syl
    @95
    eqssd
    cX
    cJ
    istopon
    sylanbrc
end
