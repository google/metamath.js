include "cdm.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "oif.mm"
include "ffn.mm"
include "mp1i.mm"
include "wss.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "word.mm"
include "oicl.mm"
include "ordelon.mm"
include "mpan.mm"
include "wi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "r19.21v.mm"
include "a1i.mm"
include "ordelss.mm"
include "sylan.mm"
include "sselda.mm"
include "pm2.27.mm"
include "syl.mm"
include "ralimdva.mm"
include "wb.mm"
include "adantr.mm"
include "sstrd.mm"
include "eqfnfv.mm"
include "fvres.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cxp.mm"
include "cin.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "ad2antrr.mm"
include "wwe.mm"
include "w3a.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "fpwwe2lem7.mm"
include "simpld.mm"
include "eqcomd.mm"
include "impbida.mm"
include "fvex.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "wrel.mm"
include "inss2.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "cop.mm"
include "anbi12d.mm"
include "simprd.mm"
include "impr.mm"
include "sylan2b.mm"
include "pm5.32da.mm"
include "brinxp2.mm"
include "df-br.mm"
include "df-3an.mm"
include "3bitr3i.mm"
include "eqrelrdv.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "fpwwe2lem3.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "sylbird.mm"
include "syld.mm"
include "com23.mm"
include "a2i.mm"
include "sylbi.mm"
include "tfis2.mm"
include "com3l.mm"
include "mpdi.mm"
include "imp.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"

theorem fpwwe2lem8
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
  assert |- ( ph -> M = ( N |` dom M ) )

  proof
    wph
    vw
    cM
    cdm
    #
    cM
    cN
    @0
    cres
    #
    @0
    cX
    cM
    wf
    cM
    @0
    wfn
    #
    wph
    cX
    cR
    cM
    fpwwe2lem9.m
    oif
    #
    @0
    cX
    cM
    ffn
    mp1i
    #
    wph
    cN
    cN
    cdm
    #
    wfn
    #
    @0
    @5
    wss
    #
    @1
    @0
    wfn
    @5
    cY
    cN
    wf
    @6
    wph
    cY
    cS
    cN
    fpwwe2lem9.n
    oif
    #
    @5
    cY
    cN
    ffn
    mp1i
    #
    fpwwe2lem9.s
    @5
    @0
    cN
    fnssres
    syl2anc
    wph
    vw
    cv
    #
    @0
    wcel
    #
    wa
    #
    @10
    cM
    cfv
    #
    @10
    cN
    cfv
    #
    @10
    @1
    cfv
    #
    wph
    @11
    @13
    @14
    wceq
    #
    wph
    @11
    @10
    con0
    wcel
    #
    @16
    @0
    word
    #
    @11
    @17
    cX
    cR
    cM
    fpwwe2lem9.m
    oicl
    #
    @0
    @10
    ordelon
    mpan
    @17
    wph
    @11
    @16
    wph
    @11
    @16
    wi
    #
    wi
    #
    wph
    vy
    cv
    #
    @0
    wcel
    #
    @22
    cM
    cfv
    #
    @22
    cN
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    vw
    vy
    @10
    @22
    wceq
    #
    @20
    @27
    wph
    @29
    @11
    @23
    @16
    @26
    @10
    @22
    @0
    eleq1
    @29
    @13
    @24
    @14
    @25
    @10
    @22
    cM
    fveq2
    @10
    @22
    cN
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @28
    vy
    @10
    wral
    #
    @21
    wi
    @17
    @30
    wph
    @27
    vy
    @10
    wral
    #
    wi
    @21
    wph
    @27
    vy
    @10
    r19.21v
    wph
    @31
    @20
    wph
    @11
    @31
    @16
    wph
    @11
    @31
    @16
    wi
    @12
    @31
    @26
    vy
    @10
    wral
    #
    @16
    @12
    @27
    @26
    vy
    @10
    @12
    @22
    @10
    wcel
    #
    wa
    @23
    @27
    @26
    wi
    @12
    @10
    @0
    @22
    wph
    @18
    @11
    @10
    @0
    wss
    #
    @18
    wph
    @19
    a1i
    @0
    @10
    ordelss
    sylan
    #
    sselda
    @23
    @26
    pm2.27
    syl
    ralimdva
    @12
    @32
    cM
    @10
    cres
    #
    cN
    @10
    cres
    #
    wceq
    #
    @16
    @12
    @38
    @22
    @36
    cfv
    #
    @22
    @37
    cfv
    #
    wceq
    #
    vy
    @10
    wral
    #
    @32
    @12
    @36
    @10
    wfn
    #
    @37
    @10
    wfn
    #
    @38
    @42
    wb
    @12
    @2
    @34
    @43
    wph
    @2
    @11
    @4
    adantr
    @35
    @0
    @10
    cM
    fnssres
    syl2anc
    @12
    @6
    @10
    @5
    wss
    @44
    wph
    @6
    @11
    @9
    adantr
    @12
    @10
    @0
    @5
    @35
    wph
    @7
    @11
    fpwwe2lem9.s
    adantr
    sstrd
    @5
    @10
    cN
    fnssres
    syl2anc
    vy
    @10
    @36
    @37
    eqfnfv
    syl2anc
    @41
    @26
    vy
    @10
    @33
    @39
    @24
    @40
    @25
    @22
    @10
    cM
    fvres
    @22
    @10
    cN
    fvres
    eqeq12d
    ralbiia
    syl6bb
    @12
    @38
    @16
    @12
    @38
    wa
    #
    cR
    ccnv
    @13
    csn
    cima
    #
    cR
    @46
    @46
    cxp
    #
    cin
    #
    cF
    co
    #
    cS
    ccnv
    @14
    csn
    cima
    #
    cS
    @50
    @50
    cxp
    #
    cin
    #
    cF
    co
    #
    @13
    @14
    @45
    @46
    @50
    @48
    @52
    cF
    @45
    vy
    @46
    @50
    @45
    @22
    @13
    cR
    wbr
    #
    @22
    @14
    cS
    wbr
    #
    @22
    @46
    wcel
    #
    @22
    @50
    wcel
    #
    @45
    @54
    @55
    @45
    @54
    wa
    #
    @55
    vz
    cv
    #
    @13
    cR
    wbr
    #
    @22
    @59
    cR
    wbr
    #
    @22
    @59
    cS
    wbr
    #
    wb
    #
    wi
    #
    @45
    vx
    vy
    vu
    cA
    @10
    @22
    @59
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
    wph
    cA
    cvv
    wcel
    @11
    @38
    fpwwe2.2
    ad2antrr
    #
    @45
    wph
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @66
    @66
    cxp
    wss
    @66
    @67
    wwe
    w3a
    @66
    @67
    cF
    co
    cA
    wcel
    wph
    @11
    @38
    simpll
    #
    fpwwe2.3
    sylan
    #
    wph
    cX
    cR
    cW
    wbr
    @11
    @38
    fpwwe2lem9.x
    ad2antrr
    #
    wph
    cY
    cS
    cW
    wbr
    @11
    @38
    fpwwe2lem9.y
    ad2antrr
    #
    fpwwe2lem9.m
    fpwwe2lem9.n
    wph
    @11
    @38
    simplr
    #
    @12
    @10
    @5
    wcel
    #
    @38
    wph
    @0
    @5
    @10
    fpwwe2lem9.s
    sselda
    #
    adantr
    #
    @12
    @38
    simpr
    #
    fpwwe2lem7
    #
    simpld
    @45
    @55
    wa
    @54
    @59
    @14
    cS
    wbr
    @62
    @61
    wb
    wi
    @45
    vx
    vy
    vu
    cA
    @10
    @22
    @59
    cS
    cR
    cF
    cN
    cM
    cW
    cY
    cX
    vr
    fpwwe2.1
    @65
    @69
    @71
    @70
    fpwwe2lem9.n
    fpwwe2lem9.m
    @75
    @72
    @45
    @36
    @37
    @76
    eqcomd
    fpwwe2lem7
    simpld
    impbida
    @13
    cvv
    wcel
    #
    @56
    @54
    wb
    @10
    cM
    fvex
    #
    cR
    @13
    @22
    cvv
    vy
    vex
    #
    eliniseg
    #
    ax-mp
    @14
    cvv
    wcel
    @57
    @55
    wb
    @10
    cN
    fvex
    cS
    @14
    @22
    cvv
    @80
    eliniseg
    ax-mp
    3bitr4g
    eqrdv
    #
    @45
    @48
    cS
    @47
    cin
    #
    @52
    @45
    vy
    vz
    @48
    @83
    @48
    @47
    wss
    @47
    wrel
    #
    @48
    wrel
    cR
    @47
    inss2
    @46
    @46
    relxp
    #
    @48
    @47
    relss
    mp2
    @83
    @47
    wss
    @84
    @83
    wrel
    cS
    @47
    inss2
    @85
    @83
    @47
    relss
    mp2
    @45
    @56
    @59
    @46
    wcel
    #
    wa
    #
    @61
    wa
    #
    @87
    @62
    wa
    #
    @22
    @59
    cop
    #
    @48
    wcel
    #
    @90
    @83
    wcel
    #
    @45
    @87
    @61
    @62
    @87
    @45
    @54
    @60
    wa
    #
    @63
    @78
    @87
    @93
    wb
    @79
    @78
    @56
    @54
    @86
    @60
    @81
    cR
    @13
    @59
    cvv
    vz
    vex
    eliniseg
    anbi12d
    ax-mp
    @45
    @54
    @60
    @63
    @58
    @55
    @64
    @77
    simprd
    impr
    sylan2b
    pm5.32da
    @22
    @59
    @48
    wbr
    @56
    @86
    @61
    w3a
    @91
    @88
    @22
    @59
    @46
    @46
    cR
    brinxp2
    @22
    @59
    @48
    df-br
    @56
    @86
    @61
    df-3an
    3bitr3i
    @22
    @59
    @83
    wbr
    @56
    @86
    @62
    w3a
    @92
    @89
    @22
    @59
    @46
    @46
    cS
    brinxp2
    @22
    @59
    @83
    df-br
    @56
    @86
    @62
    df-3an
    3bitr3i
    3bitr4g
    eqrelrdv
    @45
    @47
    @51
    cS
    @45
    @46
    @50
    @82
    sqxpeqd
    ineq2d
    eqtrd
    oveq12d
    @45
    wph
    @13
    cX
    wcel
    #
    @49
    @13
    wceq
    @68
    @12
    @94
    @38
    @11
    @94
    wph
    @0
    cX
    @10
    cM
    @3
    ffvelrni
    adantl
    adantr
    wph
    vx
    vy
    vu
    cA
    @13
    cR
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem9.x
    fpwwe2lem3
    syl2anc
    @45
    wph
    @14
    cY
    wcel
    #
    @53
    @14
    wceq
    @68
    @12
    @95
    @38
    @12
    @73
    @95
    @74
    @5
    cY
    @10
    cN
    @8
    ffvelrni
    syl
    adantr
    wph
    vx
    vy
    vu
    cA
    @14
    cS
    cF
    cW
    cY
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem9.y
    fpwwe2lem3
    syl2anc
    3eqtr3d
    ex
    sylbird
    syld
    ex
    com23
    a2i
    sylbi
    a1i
    tfis2
    com3l
    mpdi
    imp
    @11
    @15
    @14
    wceq
    wph
    @10
    @0
    cN
    fvres
    adantl
    eqtr4d
    eqfnfvd
end
