include "wss.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "cdm.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "wf1o.mm"
include "wfo.mm"
include "cep.mm"
include "wiso.mm"
include "cvv.mm"
include "wcel.mm"
include "wwe.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "wsbc.mm"
include "wral.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "syl.mm"
include "fpwwe2lem2.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpld.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "fpwwe2lem8.mm"
include "rneqd.mm"
include "eqtr3d.mm"
include "df-ima.mm"
include "syl6eqr.mm"
include "imassrn.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "wrel.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "inss2.mm"
include "mp2.mm"
include "jctir.mm"
include "cop.mm"
include "ssbrd.mm"
include "brxp.mm"
include "syl6ib.mm"
include "w3a.mm"
include "brinxp2.mm"
include "df-3an.mm"
include "bitri.mm"
include "cfv.mm"
include "simprll.mm"
include "simprr.mm"
include "wb.mm"
include "isocnv.mm"
include "adantr.mm"
include "simprlr.mm"
include "sseldd.mm"
include "isorel.mm"
include "syl12anc.mm"
include "fvex.mm"
include "epelc.mm"
include "sylib.mm"
include "cnveqd.mm"
include "wfn.mm"
include "wfun.mm"
include "f1ofn.mm"
include "fnfun.mm"
include "funcnvres.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "eleqtrd.mm"
include "fvres.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "word.mm"
include "wi.mm"
include "oicl.mm"
include "ordtr1.mm"
include "ax-mp.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "imacnvcnv.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "ex.mm"
include "syl5bi.mm"
include "breq12d.mm"
include "sylan.mm"
include "eqidd.mm"
include "isores3.mm"
include "syl3anc.mm"
include "simprl.mm"
include "3bitr4d.mm"
include "sselda.mm"
include "adantrr.mm"
include "biantrurd.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "pm5.21ndd.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "eqrelrdv2.mm"
include "mpancom.mm"

theorem fpwwe2lem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vn: setvar n
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume fpwwe2.2: |- ( ph -> A e. _V )
  assume fpwwe2.3: |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) -> ( x F r ) e. A )
  assume fpwwe2lem9.x: |- ( ph -> X W R )
  assume fpwwe2lem9.y: |- ( ph -> Y W S )
  assume fpwwe2lem9.m: |- M = OrdIso ( R , X )
  assume fpwwe2lem9.n: |- N = OrdIso ( S , Y )
  assume fpwwe2lem9.s: |- ( ph -> dom M C_ dom N )

  disjoint u y
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint u x
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X r
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint M r
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint N r
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint ph r
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint A r
  disjoint A x
  disjoint R r
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint Y r
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint S r
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint W r
  disjoint W u
  disjoint W x
  disjoint W y
  disjoint B u
  disjoint B y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint a n
  disjoint X a
  disjoint b n
  disjoint X b
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M w
  disjoint M z
  disjoint N w
  disjoint N z
  disjoint a ph
  disjoint b ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint A a
  disjoint A s
  disjoint A t
  disjoint A w
  disjoint A z
  disjoint R w
  disjoint R z
  disjoint Y w
  disjoint Y z
  disjoint S z
  disjoint W a
  disjoint W b
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint W z
  assert |- ( ph -> ( X C_ Y /\ R = ( S i^i ( Y X. X ) ) ) )

  proof
    wph
    cX
    cY
    wss
    #
    cR
    cS
    cY
    cX
    cxp
    #
    cin
    #
    wceq
    #
    wph
    cX
    cN
    cM
    cdm
    #
    cima
    #
    cY
    wph
    cX
    cN
    @4
    cres
    #
    crn
    #
    @5
    wph
    cM
    crn
    #
    cX
    @7
    wph
    @4
    cX
    cM
    wf1o
    #
    @4
    cX
    cM
    wfo
    @8
    cX
    wceq
    wph
    @4
    cX
    cep
    cR
    cM
    wiso
    #
    @9
    wph
    cX
    cvv
    wcel
    #
    cX
    cR
    wwe
    #
    @10
    wph
    cX
    cR
    cW
    wbr
    #
    @11
    fpwwe2lem9.x
    cX
    cR
    cW
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @14
    @14
    cxp
    wss
    wa
    @14
    @15
    wwe
    vu
    cv
    #
    @15
    @16
    @16
    cxp
    #
    cin
    cF
    co
    vy
    cv
    #
    wceq
    vu
    @15
    ccnv
    @18
    csn
    #
    cima
    wsbc
    vy
    @14
    wral
    wa
    wa
    vx
    vr
    cW
    fpwwe2.1
    relopabi
    #
    brrelexi
    syl
    wph
    @12
    @16
    cR
    @17
    cin
    cF
    co
    @18
    wceq
    vu
    cR
    ccnv
    @19
    cima
    wsbc
    vy
    cX
    wral
    #
    wph
    cX
    cA
    wss
    #
    cR
    cX
    cX
    cxp
    #
    wss
    #
    wa
    #
    @12
    @21
    wa
    #
    wph
    @13
    @25
    @26
    wa
    fpwwe2lem9.x
    wph
    vx
    vy
    vu
    cA
    cR
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    mpbid
    #
    simprd
    simpld
    cX
    cR
    cM
    cvv
    fpwwe2lem9.m
    oiiso
    syl2anc
    #
    @4
    cX
    cep
    cR
    cM
    isof1o
    syl
    @4
    cX
    cM
    f1ofo
    @4
    cX
    cM
    forn
    3syl
    wph
    cM
    @6
    wph
    vx
    vy
    vu
    cA
    cR
    cS
    cF
    cM
    cN
    cW
    cX
    cY
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2.3
    fpwwe2lem9.x
    fpwwe2lem9.y
    fpwwe2lem9.m
    fpwwe2lem9.n
    fpwwe2lem9.s
    fpwwe2lem8
    #
    rneqd
    eqtr3d
    cN
    @4
    df-ima
    syl6eqr
    #
    wph
    cN
    crn
    #
    @5
    cY
    cN
    @4
    imassrn
    wph
    cN
    cdm
    #
    cY
    cN
    wf1o
    #
    @32
    cY
    cN
    wfo
    @31
    cY
    wceq
    wph
    @32
    cY
    cep
    cS
    cN
    wiso
    #
    @33
    wph
    cY
    cvv
    wcel
    #
    cY
    cS
    wwe
    #
    @34
    wph
    cY
    cS
    cW
    wbr
    #
    @35
    fpwwe2lem9.y
    cY
    cS
    cW
    @20
    brrelexi
    syl
    wph
    @36
    @16
    cS
    @17
    cin
    cF
    co
    @18
    wceq
    vu
    cS
    ccnv
    @19
    cima
    wsbc
    vy
    cY
    wral
    #
    wph
    cY
    cA
    wss
    cS
    cY
    cY
    cxp
    wss
    wa
    #
    @36
    @38
    wa
    #
    wph
    @37
    @39
    @40
    wa
    fpwwe2lem9.y
    wph
    vx
    vy
    vu
    cA
    cS
    cF
    cW
    cY
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    mpbid
    simprd
    simpld
    cY
    cS
    cN
    cvv
    fpwwe2lem9.n
    oiiso
    syl2anc
    #
    @32
    cY
    cep
    cS
    cN
    isof1o
    syl
    @32
    cY
    cN
    f1ofo
    @32
    cY
    cN
    forn
    3syl
    syl5sseq
    eqsstrd
    #
    cR
    wrel
    #
    @2
    wrel
    #
    wa
    wph
    @3
    wph
    @43
    @44
    wph
    @24
    @23
    wrel
    @43
    wph
    @22
    @24
    wph
    @25
    @26
    @27
    simpld
    simprd
    #
    cX
    cX
    relxp
    cR
    @23
    relss
    mpisyl
    @2
    @1
    wss
    @1
    wrel
    @44
    cS
    @1
    inss2
    cY
    cX
    relxp
    @2
    @1
    relss
    mp2
    jctir
    wph
    vx
    vy
    cR
    @2
    wph
    @14
    @18
    cR
    wbr
    #
    @14
    @18
    @2
    wbr
    #
    @14
    @18
    cop
    #
    cR
    wcel
    @48
    @2
    wcel
    wph
    @14
    cX
    wcel
    #
    @18
    cX
    wcel
    #
    wa
    #
    @46
    @47
    wph
    @46
    @14
    @18
    @23
    wbr
    @51
    wph
    cR
    @23
    @14
    @18
    @45
    ssbrd
    @14
    @18
    cX
    cX
    brxp
    syl6ib
    @47
    @14
    cY
    wcel
    #
    @50
    wa
    #
    @14
    @18
    cS
    wbr
    #
    wa
    #
    wph
    @51
    @47
    @52
    @50
    @54
    w3a
    @55
    @14
    @18
    cY
    cX
    cS
    brinxp2
    @52
    @50
    @54
    df-3an
    bitri
    #
    wph
    @55
    @51
    wph
    @55
    wa
    #
    @49
    @50
    @57
    @14
    cN
    ccnv
    #
    ccnv
    @4
    cima
    #
    cX
    @57
    @14
    @59
    wcel
    #
    @52
    @14
    @58
    cfv
    #
    @4
    wcel
    #
    wph
    @52
    @50
    @54
    simprll
    #
    @57
    @61
    @18
    @58
    cfv
    #
    wcel
    #
    @64
    @4
    wcel
    #
    @62
    @57
    @61
    @64
    cep
    wbr
    #
    @65
    @57
    @54
    @67
    wph
    @53
    @54
    simprr
    @57
    cY
    @32
    cS
    cep
    @58
    wiso
    #
    @52
    @18
    cY
    wcel
    @54
    @67
    wb
    wph
    @68
    @55
    wph
    @34
    @68
    @41
    @32
    cY
    cep
    cS
    cN
    isocnv
    syl
    adantr
    #
    @63
    @57
    cX
    cY
    @18
    wph
    @0
    @55
    @42
    adantr
    wph
    @52
    @50
    @54
    simprlr
    #
    sseldd
    cY
    @32
    @14
    @18
    cS
    cep
    @58
    isorel
    syl12anc
    mpbid
    @61
    @64
    @18
    @58
    fvex
    epelc
    sylib
    @57
    @18
    cM
    ccnv
    #
    cfv
    #
    @64
    @4
    @57
    @72
    @18
    @58
    @5
    cres
    #
    cfv
    #
    @64
    @57
    @18
    @71
    @73
    @57
    @71
    @6
    ccnv
    #
    @73
    @57
    cM
    @6
    wph
    cM
    @6
    wceq
    #
    @55
    @29
    adantr
    cnveqd
    @57
    @58
    cY
    wfn
    #
    @58
    wfun
    @75
    @73
    wceq
    @57
    @68
    cY
    @32
    @58
    wf1o
    @77
    @69
    cY
    @32
    cS
    cep
    @58
    isof1o
    cY
    @32
    @58
    f1ofn
    3syl
    #
    cY
    @58
    fnfun
    @4
    cN
    funcnvres
    3syl
    eqtrd
    fveq1d
    @57
    @18
    @5
    wcel
    #
    @74
    @64
    wceq
    @57
    @18
    cX
    @5
    @70
    wph
    cX
    @5
    wceq
    #
    @55
    @30
    adantr
    #
    eleqtrd
    @18
    @5
    @58
    fvres
    syl
    eqtrd
    @57
    cX
    @4
    @18
    @71
    wph
    cX
    @4
    @71
    wf
    #
    @55
    wph
    cX
    @4
    cR
    cep
    @71
    wiso
    #
    cX
    @4
    @71
    wf1o
    @82
    wph
    @10
    @83
    @28
    @4
    cX
    cep
    cR
    cM
    isocnv
    syl
    #
    cX
    @4
    cR
    cep
    @71
    isof1o
    cX
    @4
    @71
    f1of
    3syl
    adantr
    @70
    ffvelrnd
    eqeltrrd
    @4
    word
    @65
    @66
    wa
    @62
    wi
    cX
    cR
    cM
    fpwwe2lem9.m
    oicl
    @61
    @64
    @4
    ordtr1
    ax-mp
    syl2anc
    @57
    @77
    @60
    @52
    @62
    wa
    wb
    @78
    cY
    @14
    @4
    @58
    elpreima
    syl
    mpbir2and
    @57
    cX
    @5
    @59
    @81
    cN
    @4
    imacnvcnv
    syl6eqr
    eleqtrrd
    @70
    jca
    ex
    syl5bi
    wph
    @51
    @46
    @47
    wb
    wph
    @51
    wa
    #
    @46
    @54
    @47
    @85
    @14
    @71
    cfv
    #
    @72
    cep
    wbr
    #
    @14
    @75
    cfv
    #
    @18
    @75
    cfv
    #
    cep
    wbr
    #
    @46
    @54
    @85
    @86
    @88
    @72
    @89
    cep
    @85
    @14
    @71
    @75
    @85
    cM
    @6
    wph
    @76
    @51
    @29
    adantr
    cnveqd
    #
    fveq1d
    @85
    @18
    @71
    @75
    @91
    fveq1d
    breq12d
    wph
    @83
    @51
    @46
    @87
    wb
    @84
    cX
    @4
    @14
    @18
    cR
    cep
    @71
    isorel
    sylan
    @85
    @5
    @4
    cS
    cep
    @75
    wiso
    #
    @14
    @5
    wcel
    @79
    @54
    @90
    wb
    wph
    @92
    @51
    wph
    @4
    @5
    cep
    cS
    @6
    wiso
    #
    @92
    wph
    @34
    @4
    @32
    wss
    @5
    @5
    wceq
    @93
    @41
    fpwwe2lem9.s
    wph
    @5
    eqidd
    @32
    cY
    cep
    cS
    cN
    @4
    @5
    isores3
    syl3anc
    @4
    @5
    cep
    cS
    @6
    isocnv
    syl
    adantr
    @85
    @14
    cX
    @5
    wph
    @49
    @50
    simprl
    wph
    @80
    @51
    @30
    adantr
    #
    eleqtrd
    @85
    @18
    cX
    @5
    wph
    @49
    @50
    simprr
    #
    @94
    eleqtrd
    @5
    @4
    @14
    @18
    cS
    cep
    @75
    isorel
    syl12anc
    3bitr4d
    @85
    @54
    @55
    @47
    @85
    @53
    @54
    @85
    @52
    @50
    wph
    @49
    @52
    @50
    wph
    cX
    cY
    @14
    @42
    sselda
    adantrr
    @95
    jca
    biantrurd
    @56
    syl6bbr
    bitrd
    ex
    pm5.21ndd
    @14
    @18
    cR
    df-br
    @14
    @18
    @2
    df-br
    3bitr3g
    eqrelrdv2
    mpancom
    jca
end
