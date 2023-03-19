include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wcel.mm"
include "cin.mm"
include "cdm.mm"
include "cres.mm"
include "ccom.mm"
include "adantr.mm"
include "fveq1d.mm"
include "ccnv.mm"
include "cima.mm"
include "sseldd.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ccn.mm"
include "co.mm"
include "cnf.mm"
include "syl.mm"
include "ffn.mm"
include "elpreima.mm"
include "simprbda.mm"
include "syldan.mm"
include "fvco3.mm"
include "sylan.mm"
include "3eqtr3d.mm"
include "simplbda.mm"
include "fvres.mm"
include "crest.mm"
include "cuni.mm"
include "eqid.mm"
include "cconn.mm"
include "wss.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "crn.mm"
include "ctop.mm"
include "ccvm.mm"
include "cvmtop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "df-ima.mm"
include "elssuni.mm"
include "cvmsuni.mm"
include "sseqtrd.mm"
include "imass2.mm"
include "cnveqd.mm"
include "cnvco.mm"
include "3eqtr3g.mm"
include "imaeq1d.mm"
include "imaco.mm"
include "wfun.mm"
include "ffun.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "cvmcn.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "df-ss.mm"
include "cvv.mm"
include "topopn.mm"
include "ssexd.mm"
include "cvmsss.mm"
include "elrestr.mm"
include "eqeltrrd.mm"
include "ccld.mm"
include "cvmscld.mm"
include "conntop.mm"
include "restuni.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "conncn.mm"
include "feq2d.mm"
include "ffvelrnd.mm"
include "3eqtr4d.mm"
include "wf1.mm"
include "wf1o.mm"
include "cvmsf1o.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "ex.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab3.mm"
include "3imtr4d.mm"
include "fndmin.mm"
include "eleq2d.mm"

theorem cvmliftmolem1
  let wph: wff ph
  let wps: wff ps
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vr: setvar r
  let vw: setvar w
  let cG: class G
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  let cP: class P
  assume cvmliftmo.b: |- B = U. C
  assume cvmliftmo.y: |- Y = U. K
  assume cvmliftmo.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftmo.k: |- ( ph -> K e. Conn )
  assume cvmliftmo.l: |- ( ph -> K e. N-Locally Conn )
  assume cvmliftmo.o: |- ( ph -> O e. Y )
  assume cvmliftmoi.m: |- ( ph -> M e. ( K Cn C ) )
  assume cvmliftmoi.n: |- ( ph -> N e. ( K Cn C ) )
  assume cvmliftmoi.g: |- ( ph -> ( F o. M ) = ( F o. N ) )
  assume cvmliftmoi.p: |- ( ph -> ( M ` O ) = ( N ` O ) )
  assume cvmliftmolem.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmliftmolem.2: |- ( ( ph /\ ps ) -> T e. ( S ` U ) )
  assume cvmliftmolem.3: |- ( ( ph /\ ps ) -> W e. T )
  assume cvmliftmolem.4: |- ( ( ph /\ ps ) -> I C_ ( `' M " W ) )
  assume cvmliftmolem.5: |- ( ( ph /\ ps ) -> ( K |`t I ) e. Conn )
  assume cvmliftmolem.6: |- ( ( ph /\ ps ) -> X e. I )
  assume cvmliftmolem.7: |- ( ( ph /\ ps ) -> Q e. I )
  assume cvmliftmolem.8: |- ( ( ph /\ ps ) -> R e. I )
  assume cvmliftmolem.9: |- ( ( ph /\ ps ) -> ( F ` ( M ` X ) ) e. U )

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint B v
  disjoint K s
  disjoint M k
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint N s
  disjoint ph s
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint S s
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint W u
  disjoint W v
  disjoint Y s
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a m
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint C a
  disjoint b f
  disjoint b g
  disjoint b k
  disjoint b m
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint C b
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint C f
  disjoint g k
  disjoint g m
  disjoint g r
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint C g
  disjoint k m
  disjoint k r
  disjoint k w
  disjoint m r
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint C m
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint C r
  disjoint s w
  disjoint u w
  disjoint v w
  disjoint C w
  disjoint G f
  disjoint G g
  disjoint a t
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b t
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint m t
  disjoint m y
  disjoint m z
  disjoint J m
  disjoint r t
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u y
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint B b
  disjoint B w
  disjoint a x
  disjoint K a
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint K f
  disjoint g t
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K g
  disjoint m x
  disjoint K m
  disjoint s x
  disjoint t x
  disjoint K t
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M a
  disjoint b x
  disjoint M b
  disjoint k x
  disjoint M m
  disjoint r x
  disjoint M r
  disjoint M t
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N a
  disjoint N m
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint O f
  disjoint O g
  disjoint O x
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q x
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F m
  disjoint F r
  disjoint F t
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint S a
  disjoint S b
  disjoint S m
  disjoint S t
  disjoint S y
  disjoint S z
  disjoint P f
  disjoint P g
  disjoint R x
  disjoint Y a
  disjoint Y m
  disjoint Y t
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( ph /\ ps ) -> ( Q e. dom ( M i^i N ) -> R e. dom ( M i^i N ) ) )

  proof
    wph
    wps
    wa
    #
    cQ
    vx
    cv
    #
    cM
    cfv
    #
    @1
    cN
    cfv
    #
    wceq
    #
    vx
    cY
    crab
    #
    wcel
    #
    cR
    @5
    wcel
    #
    cQ
    cM
    cN
    cin
    cdm
    #
    wcel
    cR
    @8
    wcel
    @0
    cQ
    cM
    cfv
    #
    cQ
    cN
    cfv
    #
    wceq
    #
    cR
    cM
    cfv
    #
    cR
    cN
    cfv
    #
    wceq
    #
    @6
    @7
    @0
    @11
    @14
    @0
    @11
    wa
    #
    @12
    cF
    cW
    cres
    #
    cfv
    #
    @13
    @16
    cfv
    #
    wceq
    #
    @14
    @15
    @12
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    @17
    @18
    @0
    @20
    @21
    wceq
    @11
    @0
    cR
    cF
    cM
    ccom
    #
    cfv
    #
    cR
    cF
    cN
    ccom
    #
    cfv
    #
    @20
    @21
    @0
    cR
    @22
    @24
    wph
    @22
    @24
    wceq
    wps
    cvmliftmoi.g
    adantr
    #
    fveq1d
    wph
    wps
    cR
    cY
    wcel
    #
    @23
    @20
    wceq
    #
    wph
    wps
    cR
    cM
    ccnv
    #
    cW
    cima
    #
    wcel
    #
    @27
    @0
    cI
    @30
    cR
    cvmliftmolem.4
    cvmliftmolem.8
    sseldd
    #
    wph
    @31
    @27
    @12
    cW
    wcel
    #
    wph
    cM
    cY
    wfn
    #
    @31
    @27
    @33
    wa
    wb
    wph
    cY
    cB
    cM
    wf
    #
    @34
    wph
    cM
    cK
    cC
    ccn
    co
    #
    wcel
    @35
    cvmliftmoi.m
    cM
    cK
    cC
    cY
    cB
    cvmliftmo.y
    cvmliftmo.b
    cnf
    syl
    #
    cY
    cB
    cM
    ffn
    syl
    #
    cY
    cR
    cW
    cM
    elpreima
    syl
    #
    simprbda
    syldan
    #
    wph
    @35
    @27
    @28
    @37
    cY
    cB
    cR
    cF
    cM
    fvco3
    sylan
    syldan
    wph
    wps
    @27
    @25
    @21
    wceq
    #
    @40
    wph
    cY
    cB
    cN
    wf
    #
    @27
    @41
    wph
    cN
    @36
    wcel
    #
    @42
    cvmliftmoi.n
    cN
    cK
    cC
    cY
    cB
    cvmliftmo.y
    cvmliftmo.b
    cnf
    syl
    #
    cY
    cB
    cR
    cF
    cN
    fvco3
    sylan
    syldan
    3eqtr3d
    adantr
    @15
    @33
    @17
    @20
    wceq
    @0
    @33
    @11
    wph
    wps
    @31
    @33
    @32
    wph
    @31
    @27
    @33
    @39
    simplbda
    syldan
    adantr
    #
    @12
    cW
    cF
    fvres
    syl
    @15
    @13
    cW
    wcel
    #
    @18
    @21
    wceq
    @15
    cR
    cN
    cI
    cres
    #
    cfv
    #
    @13
    cW
    @15
    cR
    cI
    wcel
    #
    @48
    @13
    wceq
    @0
    @49
    @11
    cvmliftmolem.8
    adantr
    #
    cR
    cI
    cN
    fvres
    syl
    @15
    cI
    cW
    cR
    @47
    @15
    cI
    cW
    @47
    wf
    cK
    cI
    crest
    co
    #
    cuni
    #
    cW
    @47
    wf
    @15
    cQ
    cW
    @47
    @51
    cC
    cF
    ccnv
    #
    cU
    cima
    #
    crest
    co
    #
    @52
    @52
    eqid
    @0
    @51
    cconn
    wcel
    @11
    cvmliftmolem.5
    adantr
    @0
    @47
    @51
    @55
    ccn
    co
    wcel
    #
    @11
    @0
    @47
    @51
    cC
    ccn
    co
    wcel
    #
    @56
    @0
    @43
    cI
    cY
    wss
    #
    @57
    wph
    @43
    wps
    cvmliftmoi.n
    adantr
    @0
    cI
    @30
    cY
    cvmliftmolem.4
    wph
    @30
    cY
    wss
    wps
    wph
    cM
    cdm
    #
    @30
    cY
    cM
    cW
    cnvimass
    wph
    @35
    @59
    cY
    wceq
    @37
    cY
    cB
    cM
    fdm
    syl
    syl5sseq
    adantr
    sstrd
    #
    cI
    cN
    cK
    cC
    cY
    cvmliftmo.y
    cnrest
    syl2anc
    @0
    cC
    cB
    ctopon
    cfv
    wcel
    #
    @47
    crn
    #
    @54
    wss
    @54
    cB
    wss
    @57
    @56
    wb
    @0
    cC
    ctop
    wcel
    #
    @61
    @0
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @63
    wph
    @64
    wps
    cvmliftmo.f
    adantr
    #
    cC
    cF
    cJ
    cvmtop1
    syl
    #
    cC
    cB
    cvmliftmo.b
    toptopon
    sylib
    @0
    @62
    cN
    cI
    cima
    #
    @54
    cN
    cI
    df-ima
    @0
    @67
    @54
    wss
    #
    cI
    cN
    ccnv
    #
    @54
    cima
    #
    wss
    #
    @0
    cI
    @29
    @54
    cima
    #
    @70
    @0
    cI
    @30
    @72
    cvmliftmolem.4
    @0
    cW
    @54
    wss
    #
    @30
    @72
    wss
    @0
    cW
    cT
    cuni
    #
    @54
    @0
    cW
    cT
    wcel
    #
    cW
    @74
    wss
    cvmliftmolem.3
    cW
    cT
    elssuni
    syl
    @0
    cT
    cU
    cS
    cfv
    wcel
    #
    @74
    @54
    wceq
    cvmliftmolem.2
    vv
    vu
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmliftmolem.1
    cvmsuni
    syl
    sseqtrd
    #
    cW
    @54
    @29
    imass2
    syl
    sstrd
    @0
    @29
    @53
    ccom
    #
    cU
    cima
    @69
    @53
    ccom
    #
    cU
    cima
    @72
    @70
    @0
    @78
    @79
    cU
    @0
    @22
    ccnv
    @24
    ccnv
    @78
    @79
    @0
    @22
    @24
    @26
    cnveqd
    cF
    cM
    cnvco
    cF
    cN
    cnvco
    3eqtr3g
    imaeq1d
    @29
    @53
    cU
    imaco
    @69
    @53
    cU
    imaco
    3eqtr3g
    sseqtrd
    @0
    cN
    wfun
    #
    cI
    cN
    cdm
    #
    wss
    @68
    @71
    wb
    @0
    @42
    @80
    wph
    @42
    wps
    @44
    adantr
    #
    cY
    cB
    cN
    ffun
    syl
    @0
    cI
    cY
    @81
    @60
    @0
    @42
    @81
    cY
    wceq
    @82
    cY
    cB
    cN
    fdm
    syl
    sseqtr4d
    cI
    @54
    cN
    funimass3
    syl2anc
    mpbird
    syl5eqssr
    @0
    cF
    cdm
    #
    @54
    cB
    cF
    cU
    cnvimass
    wph
    @83
    cB
    wceq
    #
    wps
    wph
    cB
    cJ
    cuni
    #
    cF
    wf
    #
    @84
    wph
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    @86
    wph
    @64
    @87
    cvmliftmo.f
    cC
    cF
    cJ
    cvmcn
    syl
    cF
    cC
    cJ
    cB
    @85
    cvmliftmo.b
    @85
    eqid
    cnf
    syl
    cB
    @85
    cF
    fdm
    syl
    adantr
    syl5sseq
    #
    @54
    @47
    @51
    cC
    cB
    cnrest2
    syl3anc
    mpbid
    adantr
    @0
    cW
    @55
    wcel
    @11
    @0
    cW
    @54
    cin
    #
    cW
    @55
    @0
    @73
    @89
    cW
    wceq
    @77
    cW
    @54
    df-ss
    sylib
    @0
    @63
    @54
    cvv
    wcel
    cW
    cC
    wcel
    @89
    @55
    wcel
    @66
    @0
    @54
    cB
    cC
    @0
    @63
    cB
    cC
    wcel
    @66
    cC
    cB
    cvmliftmo.b
    topopn
    syl
    @88
    ssexd
    @0
    cT
    cC
    cW
    @0
    @76
    cT
    cC
    wss
    cvmliftmolem.2
    vv
    vu
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmliftmolem.1
    cvmsss
    syl
    cvmliftmolem.3
    sseldd
    cW
    @54
    cC
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    adantr
    @0
    cW
    @55
    ccld
    cfv
    wcel
    #
    @11
    @0
    @64
    @76
    @75
    @90
    @65
    cvmliftmolem.2
    cvmliftmolem.3
    vv
    vu
    cW
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmliftmolem.1
    cvmscld
    syl3anc
    adantr
    @0
    cQ
    @52
    wcel
    @11
    @0
    cQ
    cI
    @52
    cvmliftmolem.7
    @0
    cK
    ctop
    wcel
    #
    @58
    cI
    @52
    wceq
    #
    wph
    @91
    wps
    wph
    cK
    cconn
    wcel
    @91
    cvmliftmo.k
    cK
    conntop
    syl
    adantr
    @60
    cI
    cK
    cY
    cvmliftmo.y
    restuni
    syl2anc
    #
    eleqtrd
    adantr
    @15
    cQ
    @47
    cfv
    #
    @10
    cW
    @15
    cQ
    cI
    wcel
    #
    @94
    @10
    wceq
    @0
    @95
    @11
    cvmliftmolem.7
    adantr
    cQ
    cI
    cN
    fvres
    syl
    @15
    @9
    @10
    cW
    @0
    @11
    simpr
    @0
    @9
    cW
    wcel
    #
    @11
    wph
    wps
    cQ
    @30
    wcel
    #
    @96
    @0
    cI
    @30
    cQ
    cvmliftmolem.4
    cvmliftmolem.7
    sseldd
    #
    wph
    @97
    cQ
    cY
    wcel
    #
    @96
    wph
    @34
    @97
    @99
    @96
    wa
    wb
    @38
    cY
    cQ
    cW
    cM
    elpreima
    syl
    #
    simplbda
    syldan
    adantr
    eqeltrrd
    eqeltrd
    conncn
    @15
    cI
    @52
    cW
    @47
    @0
    @92
    @11
    @93
    adantr
    feq2d
    mpbird
    @50
    ffvelrnd
    eqeltrrd
    #
    @13
    cW
    cF
    fvres
    syl
    3eqtr4d
    @15
    cW
    cU
    @16
    wf1
    #
    @33
    @46
    @19
    @14
    wb
    @0
    @102
    @11
    @0
    cW
    cU
    @16
    wf1o
    #
    @102
    @0
    @64
    @76
    @75
    @103
    @65
    cvmliftmolem.2
    cvmliftmolem.3
    vv
    vu
    cW
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmliftmolem.1
    cvmsf1o
    syl3anc
    cW
    cU
    @16
    f1of1
    syl
    adantr
    @45
    @101
    cW
    cU
    @12
    @13
    @16
    f1fveq
    syl12anc
    mpbid
    ex
    @0
    @99
    @6
    @11
    wb
    wph
    wps
    @97
    @99
    @98
    wph
    @97
    @99
    @96
    @100
    simprbda
    syldan
    @4
    @11
    vx
    cQ
    cY
    @1
    cQ
    wceq
    @2
    @9
    @3
    @10
    @1
    cQ
    cM
    fveq2
    @1
    cQ
    cN
    fveq2
    eqeq12d
    elrab3
    syl
    @0
    @27
    @7
    @14
    wb
    @40
    @4
    @14
    vx
    cR
    cY
    @1
    cR
    wceq
    @2
    @12
    @3
    @13
    @1
    cR
    cM
    fveq2
    @1
    cR
    cN
    fveq2
    eqeq12d
    elrab3
    syl
    3imtr4d
    @0
    @8
    @5
    cQ
    wph
    @8
    @5
    wceq
    #
    wps
    wph
    @34
    cN
    cY
    wfn
    #
    @104
    @38
    wph
    @42
    @105
    @44
    cY
    cB
    cN
    ffn
    syl
    vx
    cY
    cM
    cN
    fndmin
    syl2anc
    adantr
    #
    eleq2d
    @0
    @8
    @5
    cR
    @106
    eleq2d
    3imtr4d
end
