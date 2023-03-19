include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cxp.mm"
include "wss.mm"
include "wwe.mm"
include "cv.mm"
include "cin.mm"
include "co.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "fpwwe2lem2.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "ssbrd.mm"
include "brxp.mm"
include "simplbi.mm"
include "syl6.mm"
include "imp.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "wf1o.mm"
include "wfo.mm"
include "cep.mm"
include "wiso.mm"
include "cvv.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "syl.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "adantr.mm"
include "isof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "f1ocnvfv2.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "isorel.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "epelg.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "imacnvcnv.mm"
include "syl6eleq.mm"
include "cres.mm"
include "rneqd.mm"
include "df-ima.mm"
include "3eqtr4g.mm"
include "eleqtrd.mm"
include "sseldd.mm"
include "cnveqd.mm"
include "wfun.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "funcnvres.mm"
include "3eqtr3d.mm"
include "fveq1d.mm"
include "fvres.mm"
include "3jca.mm"

theorem fpwwe2lem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
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
  assume fpwwe2lem7.1: |- ( ph -> B e. dom M )
  assume fpwwe2lem7.2: |- ( ph -> B e. dom N )
  assume fpwwe2lem7.3: |- ( ph -> ( M |` B ) = ( N |` B ) )

  disjoint u y
  disjoint B u
  disjoint B y
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
  assert |- ( ( ph /\ C R ( M ` B ) ) -> ( C e. X /\ C e. Y /\ ( `' M ` C ) = ( `' N ` C ) ) )

  proof
    wph
    cC
    cB
    cM
    cfv
    #
    cR
    wbr
    #
    wa
    #
    cC
    cX
    wcel
    #
    cC
    cY
    wcel
    cC
    cM
    ccnv
    #
    cfv
    #
    cC
    cN
    ccnv
    #
    cfv
    #
    wceq
    wph
    @1
    @3
    wph
    @1
    cC
    @0
    cX
    cX
    cxp
    #
    wbr
    #
    @3
    wph
    cR
    @8
    cC
    @0
    wph
    cX
    cA
    wss
    #
    cR
    @8
    wss
    #
    wph
    @10
    @11
    wa
    #
    cX
    cR
    wwe
    #
    vu
    cv
    #
    cR
    @14
    @14
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
    cR
    ccnv
    @16
    csn
    #
    cima
    wsbc
    vy
    cX
    wral
    #
    wa
    #
    wph
    cX
    cR
    cW
    wbr
    #
    @12
    @19
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
    simpld
    simprd
    ssbrd
    @9
    @3
    @0
    cX
    wcel
    cC
    @0
    cX
    cX
    brxp
    simplbi
    syl6
    imp
    #
    @2
    cN
    cB
    cima
    #
    cY
    cC
    @2
    cN
    crn
    #
    @23
    cY
    cN
    cB
    imassrn
    @2
    cN
    cdm
    #
    cY
    cN
    wf1o
    #
    @25
    cY
    cN
    wfo
    #
    @24
    cY
    wceq
    @2
    @25
    cY
    cep
    cS
    cN
    wiso
    #
    @26
    wph
    @28
    @1
    wph
    cY
    cvv
    wcel
    #
    cY
    cS
    wwe
    #
    @28
    wph
    cY
    cS
    cW
    wbr
    #
    @29
    fpwwe2lem9.y
    cY
    cS
    cW
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @32
    @32
    cxp
    wss
    wa
    @32
    @33
    wwe
    @14
    @33
    @15
    cin
    cF
    co
    @16
    wceq
    vu
    @33
    ccnv
    @17
    cima
    wsbc
    vy
    @32
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
    @30
    @14
    cS
    @15
    cin
    cF
    co
    @16
    wceq
    vu
    cS
    ccnv
    @17
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
    @30
    @35
    wa
    #
    wph
    @31
    @36
    @37
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
    adantr
    @25
    cY
    cep
    cS
    cN
    isof1o
    syl
    #
    @25
    cY
    cN
    f1ofo
    @25
    cY
    cN
    forn
    3syl
    syl5sseq
    @2
    cC
    cM
    cB
    cima
    #
    @23
    @2
    cC
    @4
    ccnv
    cB
    cima
    #
    @39
    @2
    cC
    @40
    wcel
    #
    @3
    @5
    cB
    wcel
    #
    @22
    @2
    @5
    cB
    cep
    wbr
    #
    @42
    @2
    @43
    @5
    cM
    cfv
    #
    @0
    cR
    wbr
    #
    @2
    @44
    cC
    @0
    cR
    @2
    cM
    cdm
    #
    cX
    cM
    wf1o
    #
    @3
    @44
    cC
    wceq
    @2
    @46
    cX
    cep
    cR
    cM
    wiso
    #
    @47
    wph
    @48
    @1
    wph
    cX
    cvv
    wcel
    #
    @13
    @48
    wph
    @20
    @49
    fpwwe2lem9.x
    cX
    cR
    cW
    @34
    brrelexi
    syl
    wph
    @13
    @18
    wph
    @12
    @19
    @21
    simprd
    simpld
    cX
    cR
    cM
    cvv
    fpwwe2lem9.m
    oiiso
    syl2anc
    adantr
    #
    @46
    cX
    cep
    cR
    cM
    isof1o
    syl
    #
    @22
    @46
    cX
    cC
    cM
    f1ocnvfv2
    syl2anc
    wph
    @1
    simpr
    eqbrtrd
    @2
    @48
    @5
    @46
    wcel
    cB
    @46
    wcel
    #
    @43
    @45
    wb
    @50
    @2
    cX
    @46
    cC
    @4
    @2
    @47
    cX
    @46
    @4
    wf1o
    cX
    @46
    @4
    wf
    #
    @51
    @46
    cX
    cM
    f1ocnv
    cX
    @46
    @4
    f1of
    3syl
    #
    @22
    ffvelrnd
    wph
    @52
    @1
    fpwwe2lem7.1
    adantr
    #
    @46
    cX
    @5
    cB
    cep
    cR
    cM
    isorel
    syl12anc
    mpbird
    @2
    @52
    @43
    @42
    wb
    @55
    @5
    cB
    @46
    epelg
    syl
    mpbid
    @2
    @53
    @4
    cX
    wfn
    @41
    @3
    @42
    wa
    wb
    @54
    cX
    @46
    @4
    ffn
    cX
    cC
    cB
    @4
    elpreima
    3syl
    mpbir2and
    cM
    cB
    imacnvcnv
    syl6eleq
    #
    @2
    cM
    cB
    cres
    #
    crn
    cN
    cB
    cres
    #
    crn
    @39
    @23
    @2
    @57
    @58
    wph
    @57
    @58
    wceq
    @1
    fpwwe2lem7.3
    adantr
    #
    rneqd
    cM
    cB
    df-ima
    cN
    cB
    df-ima
    3eqtr4g
    eleqtrd
    #
    sseldd
    @2
    cC
    @4
    @39
    cres
    #
    cfv
    #
    cC
    @6
    @23
    cres
    #
    cfv
    #
    @5
    @7
    @2
    cC
    @61
    @63
    @2
    @57
    ccnv
    #
    @58
    ccnv
    #
    @61
    @63
    @2
    @57
    @58
    @59
    cnveqd
    @2
    @47
    @4
    wfun
    #
    @65
    @61
    wceq
    @51
    @47
    @46
    cX
    cM
    wfo
    @67
    @46
    cX
    cM
    dff1o3
    simprbi
    cB
    cM
    funcnvres
    3syl
    @2
    @26
    @6
    wfun
    #
    @66
    @63
    wceq
    @38
    @26
    @27
    @68
    @25
    cY
    cN
    dff1o3
    simprbi
    cB
    cN
    funcnvres
    3syl
    3eqtr3d
    fveq1d
    @2
    cC
    @39
    wcel
    @62
    @5
    wceq
    @56
    cC
    @39
    @4
    fvres
    syl
    @2
    cC
    @23
    wcel
    @64
    @7
    wceq
    @60
    cC
    @23
    @6
    fvres
    syl
    3eqtr3d
    3jca
end
