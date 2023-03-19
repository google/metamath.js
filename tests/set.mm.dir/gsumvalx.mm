include "cvv.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "crn.mm"
include "wss.mm"
include "c0g.mm"
include "cdm.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "ccnv.mm"
include "cdif.mm"
include "cima.mm"
include "wsbc.mm"
include "cif.mm"
include "csb.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "df-gsum.mm"
include "a1i.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "weq.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "csbeq1d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex2.mm"
include "simplrr.mm"
include "rneqd.mm"
include "simpr.mm"
include "sseq12d.mm"
include "adantr.mm"
include "dmeqd.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "seqeq2d.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "exbidv.mm"
include "iotabidv.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "3eqtr4d.mm"
include "sbceq1d.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "fveq2.mm"
include "adantl.mm"
include "oveq2d.mm"
include "f1oeq2.mm"
include "syl.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "coeq1d.mm"
include "fveq12d.mm"
include "sbcied.mm"
include "ifbieq12d.mm"
include "csbied.mm"
include "elexd.mm"
include "iotaex.mm"
include "ifex.mm"
include "ovmpt2d.mm"

theorem gsumvalx
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vs: setvar s
  let vg: setvar g
  let vo: setvar o
  let vw: setvar w
  let vy: setvar y
  assume gsumval.b: |- B = ( Base ` G )
  assume gsumval.z: |- .0. = ( 0g ` G )
  assume gsumval.p: |- .+ = ( +g ` G )
  assume gsumval.o: |- O = { s e. B | A. t e. B ( ( s .+ t ) = t /\ ( t .+ s ) = t ) }
  assume gsumval.w: |- ( ph -> W = ( `' F " ( _V \ O ) ) )
  assume gsumval.g: |- ( ph -> G e. V )
  assume gsumvalx.f: |- ( ph -> F e. X )
  assume gsumvalx.a: |- ( ph -> dom F = A )

  disjoint s t
  disjoint s x
  disjoint B s
  disjoint t x
  disjoint B t
  disjoint B x
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f ph
  disjoint m n
  disjoint m x
  disjoint m ph
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint .+ s
  disjoint .+ t
  disjoint .+ x
  disjoint O f
  disjoint O m
  disjoint O n
  disjoint O x
  disjoint g o
  disjoint g w
  disjoint .0. g
  disjoint o w
  disjoint .0. o
  disjoint .0. w
  disjoint s y
  disjoint t y
  disjoint x y
  disjoint B y
  disjoint f g
  disjoint f o
  disjoint f w
  disjoint f y
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g ph
  disjoint m o
  disjoint m w
  disjoint m y
  disjoint n o
  disjoint n w
  disjoint n y
  disjoint o x
  disjoint o y
  disjoint o ph
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint ph y
  disjoint F g
  disjoint F o
  disjoint F w
  disjoint F y
  disjoint G g
  disjoint G o
  disjoint G w
  disjoint G y
  disjoint W g
  disjoint W o
  disjoint W w
  disjoint W y
  disjoint g s
  disjoint g t
  disjoint .+ g
  disjoint o s
  disjoint o t
  disjoint .+ o
  disjoint s w
  disjoint t w
  disjoint .+ w
  disjoint .+ y
  disjoint A g
  disjoint A o
  disjoint A w
  disjoint O g
  disjoint O o
  disjoint O w
  disjoint O y
  assert |- ( ph -> ( G gsum F ) = if ( ran F C_ O , .0. , if ( A e. ran ... , ( iota x E. m E. n e. ( ZZ>= ` m ) ( A = ( m ... n ) /\ x = ( seq m ( .+ , F ) ` n ) ) ) , ( iota x E. f ( f : ( 1 ... ( # ` W ) ) -1-1-onto-> W /\ x = ( seq 1 ( .+ , ( F o. f ) ) ` ( # ` W ) ) ) ) ) ) )

  proof
    wph
    vw
    vg
    cG
    cF
    cvv
    cvv
    vo
    vx
    cv
    #
    vy
    cv
    #
    vw
    cv
    #
    cplusg
    cfv
    #
    co
    #
    @1
    wceq
    #
    @1
    @0
    @3
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    @2
    cbs
    cfv
    #
    wral
    #
    vx
    @9
    crab
    #
    vg
    cv
    #
    crn
    #
    vo
    cv
    #
    wss
    #
    @2
    c0g
    cfv
    #
    @12
    cdm
    #
    cfz
    crn
    #
    wcel
    #
    @17
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    #
    wceq
    #
    @0
    @21
    @3
    @12
    @20
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @20
    cuz
    cfv
    #
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    @1
    chash
    cfv
    #
    cfz
    co
    #
    @1
    vf
    cv
    #
    wf1o
    #
    @0
    @32
    @3
    @12
    @34
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    @12
    ccnv
    #
    cvv
    @14
    cdif
    #
    cima
    #
    wsbc
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    #
    csb
    #
    cF
    crn
    #
    cO
    wss
    #
    c.0
    cA
    @18
    wcel
    #
    cA
    @22
    wceq
    #
    @0
    @21
    c.pl
    cF
    @20
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @28
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    #
    cW
    @34
    wf1o
    #
    @0
    @61
    c.pl
    cF
    @34
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    #
    cgsu
    cvv
    cgsu
    vw
    vg
    cvv
    cvv
    @49
    cmpt2
    wceq
    wph
    vx
    vy
    vw
    vg
    vf
    vm
    vn
    vo
    df-gsum
    a1i
    wph
    @2
    cG
    wceq
    #
    @12
    cF
    wceq
    #
    wa
    #
    wa
    #
    @49
    vo
    cO
    @48
    csb
    @72
    @76
    vo
    @11
    cO
    @48
    @76
    @11
    @0
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @0
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    crab
    #
    cO
    @76
    @10
    @82
    vx
    @9
    cB
    @76
    @9
    cG
    cbs
    cfv
    #
    cB
    @76
    @2
    cG
    cbs
    wph
    @73
    @74
    simprl
    #
    fveq2d
    gsumval.b
    syl6eqr
    #
    @76
    @8
    @81
    vy
    @9
    cB
    @86
    @76
    @5
    @78
    @7
    @80
    @76
    @4
    @77
    @1
    @76
    @3
    c.pl
    @0
    @1
    @76
    @3
    cG
    cplusg
    cfv
    c.pl
    @76
    @2
    cG
    cplusg
    @85
    fveq2d
    gsumval.p
    syl6eqr
    #
    oveqd
    eqeq1d
    @76
    @6
    @79
    @1
    @76
    @3
    c.pl
    @1
    @0
    @87
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    rabeqbidv
    cO
    vs
    cv
    #
    vt
    cv
    #
    c.pl
    co
    #
    @89
    wceq
    #
    @89
    @88
    c.pl
    co
    #
    @89
    wceq
    #
    wa
    #
    vt
    cB
    wral
    #
    vs
    cB
    crab
    @83
    gsumval.o
    @95
    @82
    vs
    vx
    cB
    @95
    @88
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @88
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cB
    wral
    vs
    vx
    weq
    #
    @82
    @94
    @100
    vt
    vy
    cB
    vt
    vy
    weq
    #
    @91
    @97
    @93
    @99
    @102
    @90
    @96
    @89
    @1
    @89
    @1
    @88
    c.pl
    oveq2
    @102
    id
    #
    eqeq12d
    @102
    @92
    @98
    @89
    @1
    @89
    @1
    @88
    c.pl
    oveq1
    @103
    eqeq12d
    anbi12d
    cbvralv
    @101
    @100
    @81
    vy
    cB
    @101
    @97
    @78
    @99
    @80
    @101
    @96
    @77
    @1
    @88
    @0
    @1
    c.pl
    oveq1
    eqeq1d
    @101
    @98
    @79
    @1
    @88
    @0
    @1
    c.pl
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    syl5bb
    cbvrabv
    eqtri
    syl6eqr
    csbeq1d
    @76
    vo
    cO
    @48
    @72
    cvv
    cO
    cvv
    wcel
    @76
    @95
    vs
    cB
    cO
    gsumval.o
    cB
    @84
    cvv
    gsumval.b
    cG
    cbs
    fvex
    eqeltri
    rabex2
    a1i
    @76
    @14
    cO
    wceq
    #
    wa
    #
    @15
    @51
    @16
    @47
    c.0
    @71
    @105
    @13
    @50
    @14
    cO
    @105
    @12
    cF
    wph
    @73
    @74
    @104
    simplrr
    #
    rneqd
    @76
    @104
    simpr
    #
    sseq12d
    @105
    @16
    cG
    c0g
    cfv
    #
    c.0
    @105
    @2
    cG
    c0g
    @76
    @73
    @104
    @85
    adantr
    fveq2d
    gsumval.z
    syl6eqr
    @105
    @19
    @52
    @31
    @46
    @60
    @70
    @105
    @17
    cA
    @18
    @105
    @17
    cF
    cdm
    #
    cA
    @105
    @12
    cF
    @106
    dmeqd
    wph
    @109
    cA
    wceq
    @75
    @104
    gsumvalx.a
    ad2antrr
    eqtrd
    #
    eleq1d
    @105
    @30
    @59
    vx
    @105
    @29
    @58
    vm
    @105
    @27
    @57
    vn
    @28
    @105
    @23
    @53
    @26
    @56
    @105
    @17
    cA
    @22
    @110
    eqeq1d
    @105
    @25
    @55
    @0
    @105
    @21
    @24
    @54
    @105
    @24
    c.pl
    @12
    @20
    cseq
    @54
    @105
    @3
    c.pl
    @12
    @20
    @76
    @3
    c.pl
    wceq
    @104
    @87
    adantr
    #
    seqeq2d
    @105
    @12
    cF
    c.pl
    @20
    @106
    seqeq3d
    eqtrd
    fveq1d
    eqeq2d
    anbi12d
    rexbidv
    exbidv
    iotabidv
    @105
    @45
    @69
    vx
    @105
    @44
    @68
    vf
    @105
    @44
    @40
    vy
    cW
    wsbc
    @68
    @105
    @40
    vy
    @43
    cW
    @105
    cF
    ccnv
    #
    @42
    cima
    @112
    cvv
    cO
    cdif
    #
    cima
    #
    @43
    cW
    @105
    @42
    @113
    @112
    @105
    @14
    cO
    cvv
    @107
    difeq2d
    imaeq2d
    @105
    @41
    @112
    @42
    @105
    @12
    cF
    @106
    cnveqd
    imaeq1d
    wph
    cW
    @114
    wceq
    @75
    @104
    gsumval.w
    ad2antrr
    3eqtr4d
    sbceq1d
    @105
    @40
    @68
    vy
    cW
    cvv
    wph
    cW
    cvv
    wcel
    @75
    @104
    wph
    cW
    @114
    cvv
    gsumval.w
    wph
    cF
    cX
    wcel
    @112
    cvv
    wcel
    @114
    cvv
    wcel
    gsumvalx.f
    cF
    cX
    cnvexg
    @112
    @113
    cvv
    imaexg
    3syl
    eqeltrd
    ad2antrr
    @105
    @1
    cW
    wceq
    #
    wa
    #
    @35
    @63
    @39
    @67
    @116
    @35
    @62
    @1
    @34
    wf1o
    #
    @63
    @116
    @33
    @62
    wceq
    @35
    @117
    wb
    @116
    @32
    @61
    c1
    cfz
    @115
    @32
    @61
    wceq
    @105
    @1
    cW
    chash
    fveq2
    adantl
    #
    oveq2d
    @33
    @62
    @1
    @34
    f1oeq2
    syl
    @115
    @117
    @63
    wb
    @105
    @1
    cW
    @62
    @34
    f1oeq3
    adantl
    bitrd
    @116
    @38
    @66
    @0
    @116
    @32
    @61
    @37
    @65
    @105
    @37
    @65
    wceq
    @115
    @105
    @37
    c.pl
    @36
    c1
    cseq
    @65
    @105
    @3
    c.pl
    @36
    c1
    @111
    seqeq2d
    @105
    @36
    @64
    c.pl
    c1
    @105
    @12
    cF
    @34
    @106
    coeq1d
    seqeq3d
    eqtrd
    adantr
    @118
    fveq12d
    eqeq2d
    anbi12d
    sbcied
    bitrd
    exbidv
    iotabidv
    ifbieq12d
    ifbieq12d
    csbied
    eqtrd
    wph
    cG
    cV
    gsumval.g
    elexd
    wph
    cF
    cX
    gsumvalx.f
    elexd
    @72
    cvv
    wcel
    wph
    @51
    c.0
    @71
    c.0
    @108
    cvv
    gsumval.z
    cG
    c0g
    fvex
    eqeltri
    @52
    @60
    @70
    @59
    vx
    iotaex
    @69
    vx
    iotaex
    ifex
    ifex
    a1i
    ovmpt2d
end
