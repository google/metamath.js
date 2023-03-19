include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cuni.mm"
include "ctop.mm"
include "ctopon.mm"
include "neibastop1.mm"
include "topontop.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "neii1.mm"
include "sylan.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "sseqtr4d.mm"
include "cv.mm"
include "wrex.mm"
include "neii2.mm"
include "wral.mm"
include "wi.mm"
include "weq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "raleqbi1dv.mm"
include "elrab2.mm"
include "simprrr.mm"
include "sspwb.mm"
include "sylib.mm"
include "sslin.mm"
include "simprrl.mm"
include "wb.mm"
include "snssg.mm"
include "ad3antlr.mm"
include "mpbird.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "rspcv.mm"
include "ssn0.mm"
include "syl6an.mm"
include "expr.mm"
include "com23.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "jca.mm"
include "ex.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "simprl.mm"
include "sseqtrd.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "crab.mm"
include "cdif.mm"
include "wf.mm"
include "w3a.mm"
include "simpll.mm"
include "simplr.mm"
include "elpwid.mm"
include "cbviunv.mm"
include "iuneq2d.mm"
include "syl5eq.mm"
include "mpteq2i.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "cbvrexv.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "neibastop2lem.mm"
include "eleqtrd.mm"
include "isneip.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "exlimdv.mm"
include "impbid.mm"

theorem neibastop2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cP: class P
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let cS: class S
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume neibastop1.1: |- ( ph -> X e. V )
  assume neibastop1.2: |- ( ph -> F : X --> ( ~P ~P X \ { (/) } ) )
  assume neibastop1.3: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) /\ w e. ( F ` x ) ) ) -> ( ( F ` x ) i^i ~P ( v i^i w ) ) =/= (/) )
  assume neibastop1.4: |- J = { o e. ~P X | A. x e. o ( ( F ` x ) i^i ~P o ) =/= (/) }
  assume neibastop1.5: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> x e. v )
  assume neibastop1.6: |- ( ( ph /\ ( x e. X /\ v e. ( F ` x ) ) ) -> E. t e. ( F ` x ) A. y e. t ( ( F ` y ) i^i ~P v ) =/= (/) )

  disjoint t v
  disjoint t y
  disjoint v y
  disjoint v x
  disjoint J v
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint o t
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint P o
  disjoint t w
  disjoint t x
  disjoint P t
  disjoint v w
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint N o
  disjoint N t
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint F o
  disjoint F t
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint o ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint X o
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
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
  disjoint t z
  disjoint G t
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
  disjoint x z
  disjoint J z
  disjoint f o
  disjoint f s
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint P f
  disjoint o s
  disjoint o u
  disjoint o z
  disjoint s t
  disjoint s w
  disjoint P s
  disjoint t u
  disjoint u w
  disjoint P u
  disjoint w z
  disjoint P z
  disjoint N f
  disjoint k o
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint N k
  disjoint N s
  disjoint N u
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
  disjoint F u
  disjoint F z
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph s
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X g
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X s
  disjoint X u
  disjoint X z
  assert |- ( ( ph /\ P e. X ) -> ( N e. ( ( nei ` J ) ` { P } ) <-> ( N C_ X /\ ( ( F ` P ) i^i ~P N ) =/= (/) ) ) )

  proof
    wph
    cP
    cX
    wcel
    #
    wa
    #
    cN
    cP
    csn
    #
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cN
    cX
    wss
    #
    cP
    cF
    cfv
    #
    cN
    cpw
    #
    cin
    #
    c0
    wne
    #
    wa
    #
    @1
    @3
    @9
    @1
    @3
    wa
    #
    @4
    @8
    @10
    cN
    cJ
    cuni
    #
    cX
    @1
    cJ
    ctop
    wcel
    #
    @3
    cN
    @11
    wss
    #
    wph
    @12
    @0
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @12
    wph
    vx
    vw
    vv
    vo
    cF
    cJ
    cV
    cX
    neibastop1.1
    neibastop1.2
    neibastop1.3
    neibastop1.4
    neibastop1
    #
    cX
    cJ
    topontop
    syl
    #
    adantr
    #
    @2
    cJ
    cN
    @11
    @11
    eqid
    #
    neii1
    sylan
    wph
    cX
    @11
    wceq
    #
    @0
    @3
    wph
    @14
    @19
    @15
    cX
    cJ
    toponuni
    syl
    #
    ad2antrr
    sseqtr4d
    @10
    @2
    vy
    cv
    #
    wss
    #
    @21
    cN
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    @8
    @1
    @12
    @3
    @25
    @17
    @2
    vy
    cJ
    cN
    neii2
    sylan
    @10
    @24
    @8
    vy
    cJ
    @21
    cJ
    wcel
    @21
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
    @21
    cpw
    #
    cin
    #
    c0
    wne
    #
    vx
    @21
    wral
    #
    wa
    @10
    @24
    @8
    wi
    #
    @29
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
    @35
    wral
    @33
    vo
    @21
    @26
    cJ
    @38
    @32
    vx
    @35
    @21
    vo
    vy
    weq
    #
    @37
    @31
    c0
    @39
    @36
    @30
    @29
    @35
    @21
    pweq
    ineq2d
    neeq1d
    raleqbi1dv
    neibastop1.4
    elrab2
    @10
    @27
    @33
    @34
    @10
    @27
    wa
    @24
    @33
    @8
    @10
    @27
    @24
    @33
    @8
    wi
    @10
    @27
    @24
    wa
    #
    wa
    #
    @5
    @30
    cin
    #
    @7
    wss
    #
    @33
    @42
    c0
    wne
    #
    @8
    @41
    @30
    @6
    wss
    #
    @43
    @41
    @23
    @45
    @10
    @27
    @22
    @23
    simprrr
    @21
    cN
    sspwb
    sylib
    @30
    @6
    @5
    sslin
    syl
    @41
    cP
    @21
    wcel
    #
    @33
    @44
    wi
    @41
    @46
    @22
    @10
    @27
    @22
    @23
    simprrl
    @0
    @46
    @22
    wb
    wph
    @3
    @40
    cP
    @21
    cX
    snssg
    ad3antlr
    mpbird
    @32
    @44
    vx
    cP
    @21
    @28
    cP
    wceq
    #
    @31
    @42
    c0
    @47
    @29
    @5
    @30
    @28
    cP
    cF
    fveq2
    ineq1d
    neeq1d
    rspcv
    syl
    @42
    @7
    ssn0
    syl6an
    expr
    com23
    expimpd
    syl5bi
    rexlimdv
    mpd
    jca
    ex
    @1
    @4
    @8
    @3
    @8
    vs
    cv
    #
    @7
    wcel
    #
    vs
    wex
    @1
    @4
    wa
    #
    @3
    vs
    @7
    n0
    @50
    @49
    @3
    vs
    @49
    @48
    @5
    wcel
    #
    @48
    @6
    wcel
    #
    wa
    #
    @50
    @3
    @48
    @5
    @6
    elin
    @1
    @4
    @53
    @3
    @1
    @4
    @53
    wa
    #
    wa
    #
    @3
    @13
    cP
    vu
    cv
    #
    wcel
    @56
    cN
    wss
    wa
    vu
    cJ
    wrex
    #
    @55
    cN
    cX
    @11
    @1
    @4
    @53
    simprl
    #
    wph
    @19
    @0
    @54
    @20
    ad2antrr
    #
    sseqtrd
    @55
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    cP
    vw
    cv
    #
    cF
    cfv
    #
    vg
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vg
    va
    cvv
    vb
    va
    cv
    #
    vn
    cX
    vn
    cv
    #
    cF
    cfv
    #
    vb
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
    @48
    csn
    #
    crdg
    #
    com
    cres
    #
    crn
    cuni
    #
    wrex
    #
    vw
    cX
    crab
    @48
    vf
    vo
    cF
    @77
    cJ
    cN
    cV
    cX
    va
    wph
    cX
    cV
    wcel
    @0
    @54
    neibastop1.1
    ad2antrr
    wph
    cX
    @26
    cpw
    c0
    csn
    cdif
    cF
    wf
    @0
    @54
    neibastop1.2
    ad2antrr
    @55
    wph
    @28
    cX
    wcel
    #
    vv
    cv
    #
    @29
    wcel
    #
    @60
    @29
    wcel
    w3a
    @29
    @81
    @60
    cin
    cpw
    cin
    c0
    wne
    wph
    @0
    @54
    simpll
    #
    neibastop1.3
    sylan
    neibastop1.4
    @55
    wph
    @80
    @82
    wa
    #
    @28
    @81
    wcel
    @83
    neibastop1.5
    sylan
    @55
    wph
    @84
    @21
    cF
    cfv
    #
    @81
    cpw
    cin
    c0
    wne
    vy
    vt
    cv
    wral
    vt
    @29
    wrex
    @83
    neibastop1.6
    sylan
    wph
    @0
    @54
    simplr
    #
    @58
    @1
    @4
    @51
    @52
    simprrl
    @55
    @48
    cN
    @1
    @4
    @51
    @52
    simprrr
    elpwid
    @76
    va
    cvv
    vz
    @66
    vx
    cX
    @29
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
    @75
    crdg
    #
    com
    @74
    @92
    wceq
    @76
    @93
    wceq
    va
    cvv
    @73
    @91
    vb
    vz
    @66
    @72
    @90
    vb
    vz
    weq
    #
    @72
    vx
    cX
    @29
    @70
    cin
    #
    ciun
    @90
    vn
    vx
    cX
    @71
    @95
    vn
    vx
    weq
    @68
    @29
    @70
    @67
    @28
    cF
    fveq2
    ineq1d
    cbviunv
    @94
    vx
    cX
    @95
    @89
    @94
    @70
    @88
    @29
    @69
    @87
    pweq
    ineq2d
    iuneq2d
    syl5eq
    cbviunv
    mpteq2i
    @75
    @74
    @92
    rdgeq1
    ax-mp
    reseq1i
    @79
    @85
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
    @78
    wrex
    #
    vw
    vy
    cX
    @79
    @61
    @97
    cin
    #
    c0
    wne
    #
    vf
    @78
    wrex
    vw
    vy
    weq
    #
    @100
    @65
    @102
    vg
    vf
    @78
    vg
    vf
    weq
    #
    @64
    @101
    c0
    @104
    @63
    @97
    @61
    @62
    @96
    pweq
    ineq2d
    neeq1d
    cbvrexv
    @103
    @102
    @99
    vf
    @78
    @103
    @101
    @98
    c0
    @103
    @61
    @85
    @97
    @60
    @21
    cF
    fveq2
    ineq1d
    neeq1d
    rexbidv
    syl5bb
    cbvrabv
    neibastop2lem
    @55
    @12
    cP
    @11
    wcel
    @3
    @13
    @57
    wa
    wb
    wph
    @12
    @0
    @54
    @16
    ad2antrr
    @55
    cP
    cX
    @11
    @86
    @59
    eleqtrd
    cP
    vu
    cJ
    cN
    @11
    @18
    isneip
    syl2anc
    mpbir2and
    expr
    syl5bi
    exlimdv
    syl5bi
    expimpd
    impbid
end
