include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "cnf.mm"
include "ffn.mm"
include "3syl.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "wral.mm"
include "cin.mm"
include "cdm.mm"
include "ccld.mm"
include "inss1.mm"
include "wb.mm"
include "wa.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "ccvm.mm"
include "cuni.mm"
include "adantr.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "cvmcn.mm"
include "eqid.mm"
include "syldan.mm"
include "cvmcov.mm"
include "syl2anc.mm"
include "wi.mm"
include "wex.mm"
include "n0.mm"
include "wss.mm"
include "crest.mm"
include "cconn.mm"
include "w3a.mm"
include "ccnv.mm"
include "crio.mm"
include "cima.mm"
include "cpw.mm"
include "cnlly.mm"
include "simprrr.mm"
include "cvmsss.mm"
include "simprll.mm"
include "ffvelrnd.mm"
include "simprrl.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "simpld.mm"
include "sseldd.mm"
include "cnima.mm"
include "simprd.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "simprr1.mm"
include "simplrr.mm"
include "adantl.mm"
include "adantrr.mm"
include "simplll.mm"
include "ad2antll.mm"
include "elpwid.mm"
include "simplr3.mm"
include "simplr2.mm"
include "adantrrr.mm"
include "cvmliftmolem1.mm"
include "impbid.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "jca.mm"
include "expr.mm"
include "reximdva.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "ctop.mm"
include "conntop.mm"
include "fndmin.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "isclo.mm"
include "mpbird.mm"
include "sseldi.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "eleqtrrd.mm"
include "ne0i.mm"
include "inss2.mm"
include "connclo.mm"
include "eqtr3d.mm"
include "rabid2.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "eqfnfvd.mm"

theorem cvmliftmolem2
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
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
  let cQ: class Q
  let cU: class U
  let cP: class P
  let cR: class R
  let cT: class T
  let cW: class W
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
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint P f
  disjoint P g
  disjoint R x
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint W u
  disjoint W v
  disjoint Y a
  disjoint Y m
  disjoint Y t
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> M = N )

  proof
    wph
    vx
    cY
    cM
    cN
    wph
    cM
    cK
    cC
    ccn
    co
    #
    wcel
    #
    cY
    cB
    cM
    wf
    #
    cM
    cY
    wfn
    #
    cvmliftmoi.m
    cM
    cK
    cC
    cY
    cB
    cvmliftmo.y
    cvmliftmo.b
    cnf
    #
    cY
    cB
    cM
    ffn
    #
    3syl
    #
    wph
    cN
    @0
    wcel
    cY
    cB
    cN
    wf
    cN
    cY
    wfn
    #
    cvmliftmoi.n
    cN
    cK
    cC
    cY
    cB
    cvmliftmo.y
    cvmliftmo.b
    cnf
    cY
    cB
    cN
    ffn
    3syl
    #
    wph
    vx
    cv
    #
    cM
    cfv
    #
    @9
    cN
    cfv
    #
    wceq
    #
    vx
    cY
    wph
    cY
    @12
    vx
    cY
    crab
    #
    wceq
    @12
    vx
    cY
    wral
    wph
    cM
    cN
    cin
    cdm
    #
    cY
    @13
    wph
    @14
    cK
    cY
    cvmliftmo.y
    cvmliftmo.k
    wph
    cK
    cK
    ccld
    cfv
    #
    cin
    #
    cK
    @14
    cK
    @15
    inss1
    wph
    @14
    @16
    wcel
    #
    @9
    vy
    cv
    #
    wcel
    #
    @9
    @14
    wcel
    #
    vz
    cv
    #
    @14
    wcel
    #
    wb
    #
    vz
    @18
    wral
    #
    wa
    #
    vy
    cK
    wrex
    #
    vx
    cY
    wral
    #
    wph
    @26
    vx
    cY
    wph
    @9
    cY
    wcel
    #
    wa
    #
    @10
    cF
    cfv
    #
    va
    cv
    #
    wcel
    #
    @31
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    va
    cJ
    wrex
    #
    @26
    @29
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @30
    cJ
    cuni
    #
    wcel
    #
    @36
    wph
    @37
    @28
    cvmliftmo.f
    adantr
    wph
    @28
    @10
    cB
    wcel
    #
    @39
    wph
    cY
    cB
    @9
    cM
    wph
    @1
    @2
    cvmliftmoi.m
    @4
    syl
    #
    ffvelrnda
    wph
    cB
    @38
    @10
    cF
    wph
    @37
    cF
    cC
    cJ
    ccn
    co
    wcel
    cB
    @38
    cF
    wf
    cvmliftmo.f
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    @38
    cvmliftmo.b
    @38
    eqid
    #
    cnf
    3syl
    ffvelrnda
    syldan
    va
    vv
    vu
    cC
    @30
    cS
    vk
    cF
    cJ
    @38
    vs
    cvmliftmolem.1
    @42
    cvmcov
    syl2anc
    @29
    @35
    @26
    va
    cJ
    wph
    @28
    @31
    cJ
    wcel
    #
    @35
    @26
    wi
    wph
    @28
    @43
    wa
    #
    wa
    #
    @32
    @34
    @26
    @34
    vt
    cv
    #
    @33
    wcel
    #
    vt
    wex
    @45
    @32
    wa
    #
    @26
    vt
    @33
    n0
    @48
    @47
    @26
    vt
    @45
    @32
    @47
    @26
    wph
    @44
    @32
    @47
    wa
    #
    @26
    wph
    @44
    @49
    wa
    #
    wa
    #
    @19
    @18
    vs
    cv
    #
    wss
    #
    cK
    @52
    crest
    co
    cconn
    wcel
    #
    w3a
    #
    vy
    cK
    wrex
    #
    vs
    cM
    ccnv
    @10
    vb
    cv
    wcel
    vb
    @46
    crio
    #
    cima
    #
    cpw
    #
    wrex
    #
    @26
    @51
    cK
    cconn
    cnlly
    wcel
    #
    @58
    cK
    wcel
    #
    @9
    @58
    wcel
    #
    @60
    wph
    @61
    @50
    cvmliftmo.l
    adantr
    @51
    @1
    @57
    cC
    wcel
    @62
    wph
    @1
    @50
    cvmliftmoi.m
    adantr
    @51
    @46
    cC
    @57
    @51
    @47
    @46
    cC
    wss
    wph
    @44
    @32
    @47
    simprrr
    #
    vv
    vu
    cC
    cS
    @46
    @31
    vk
    cF
    cJ
    vs
    cvmliftmolem.1
    cvmsss
    syl
    @51
    @57
    @46
    wcel
    #
    @10
    @57
    wcel
    #
    @51
    @37
    @47
    @40
    @32
    @65
    @66
    wa
    wph
    @37
    @50
    cvmliftmo.f
    adantr
    @64
    @51
    cY
    cB
    @9
    cM
    wph
    @2
    @50
    @41
    adantr
    #
    wph
    @28
    @43
    @49
    simprll
    #
    ffvelrnd
    wph
    @44
    @32
    @47
    simprrl
    #
    vb
    vv
    vu
    @10
    cB
    cC
    cS
    @46
    @31
    vk
    cF
    cJ
    @57
    vs
    cvmliftmolem.1
    cvmliftmo.b
    @57
    eqid
    cvmsiota
    syl13anc
    #
    simpld
    #
    sseldd
    @57
    cM
    cK
    cC
    cnima
    syl2anc
    @51
    @63
    @28
    @66
    @68
    @51
    @65
    @66
    @70
    simprd
    @51
    @2
    @3
    @63
    @28
    @66
    wa
    wb
    @67
    @5
    cY
    @9
    @57
    cM
    elpreima
    3syl
    mpbir2and
    vy
    cconn
    @9
    @58
    cK
    vs
    nlly2i
    syl3anc
    @51
    @56
    @26
    vs
    @59
    @51
    @52
    @59
    wcel
    #
    wa
    @55
    @25
    vy
    cK
    @51
    @72
    @18
    cK
    wcel
    #
    @55
    @25
    wi
    @51
    @72
    @73
    wa
    #
    @55
    @25
    @51
    @74
    @55
    wa
    #
    wa
    #
    @19
    @24
    @19
    @53
    @54
    @74
    @51
    simprr1
    @76
    @23
    vz
    @18
    @51
    @75
    @21
    @18
    wcel
    #
    @23
    wph
    @50
    @75
    @77
    wa
    #
    @23
    wph
    @50
    @78
    wa
    #
    wa
    #
    @20
    @22
    wph
    @79
    vv
    vu
    cB
    cC
    @9
    @21
    cS
    @46
    @31
    vk
    cF
    @52
    cJ
    cK
    cM
    cN
    cO
    @57
    @9
    cY
    vs
    cvmliftmo.b
    cvmliftmo.y
    cvmliftmo.f
    cvmliftmo.k
    cvmliftmo.l
    cvmliftmo.o
    cvmliftmoi.m
    cvmliftmoi.n
    cvmliftmoi.g
    cvmliftmoi.p
    cvmliftmolem.1
    @79
    @47
    wph
    @44
    @32
    @47
    @78
    simplrr
    adantl
    #
    wph
    @50
    @65
    @78
    @71
    adantrr
    #
    @80
    @52
    @58
    @78
    @72
    wph
    @50
    @72
    @73
    @55
    @77
    simplll
    ad2antll
    elpwid
    #
    @78
    @54
    wph
    @50
    @19
    @53
    @54
    @74
    @77
    simplr3
    ad2antll
    #
    @80
    @18
    @52
    @9
    @78
    @53
    wph
    @50
    @19
    @53
    @54
    @74
    @77
    simplr2
    ad2antll
    #
    wph
    @50
    @75
    @19
    @77
    @50
    @75
    wa
    @19
    wph
    @19
    @53
    @54
    @74
    @50
    simprr1
    adantl
    adantrrr
    sseldd
    #
    @86
    @80
    @18
    @52
    @21
    @85
    wph
    @50
    @75
    @77
    simprrr
    sseldd
    #
    wph
    @50
    @32
    @78
    @69
    adantrr
    #
    cvmliftmolem1
    wph
    @79
    vv
    vu
    cB
    cC
    @21
    @9
    cS
    @46
    @31
    vk
    cF
    @52
    cJ
    cK
    cM
    cN
    cO
    @57
    @9
    cY
    vs
    cvmliftmo.b
    cvmliftmo.y
    cvmliftmo.f
    cvmliftmo.k
    cvmliftmo.l
    cvmliftmo.o
    cvmliftmoi.m
    cvmliftmoi.n
    cvmliftmoi.g
    cvmliftmoi.p
    cvmliftmolem.1
    @81
    @82
    @83
    @84
    @86
    @87
    @86
    @88
    cvmliftmolem1
    impbid
    anassrs
    anassrs
    ralrimiva
    jca
    expr
    anassrs
    reximdva
    rexlimdva
    mpd
    anassrs
    expr
    exlimdv
    syl5bi
    expimpd
    anassrs
    rexlimdva
    mpd
    ralrimiva
    wph
    cK
    ctop
    wcel
    #
    @14
    cY
    wss
    @17
    @27
    wb
    wph
    cK
    cconn
    wcel
    @89
    cvmliftmo.k
    cK
    conntop
    syl
    wph
    @14
    @13
    cY
    wph
    @3
    @7
    @14
    @13
    wceq
    @6
    @8
    vx
    cY
    cM
    cN
    fndmin
    syl2anc
    #
    @12
    vx
    cY
    ssrab2
    syl6eqss
    vx
    vy
    vz
    @14
    cK
    cY
    cvmliftmo.y
    isclo
    syl2anc
    mpbird
    #
    sseldi
    wph
    cO
    @14
    wcel
    @14
    c0
    wne
    wph
    cO
    @13
    @14
    wph
    cO
    cY
    wcel
    cO
    cM
    cfv
    #
    cO
    cN
    cfv
    #
    wceq
    #
    cO
    @13
    wcel
    cvmliftmo.o
    cvmliftmoi.p
    @12
    @94
    vx
    cO
    cY
    @9
    cO
    wceq
    @10
    @92
    @11
    @93
    @9
    cO
    cM
    fveq2
    @9
    cO
    cN
    fveq2
    eqeq12d
    elrab
    sylanbrc
    @90
    eleqtrrd
    @14
    cO
    ne0i
    syl
    wph
    @16
    @15
    @14
    cK
    @15
    inss2
    @91
    sseldi
    connclo
    @90
    eqtr3d
    @12
    vx
    cY
    rabid2
    sylib
    r19.21bi
    eqfnfvd
end
