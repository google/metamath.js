include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "wi.mm"
include "ccnv.mm"
include "cdm.mm"
include "wf1o.mm"
include "wcel.mm"
include "wceq.mm"
include "cep.mm"
include "wiso.mm"
include "cvv.mm"
include "wwe.mm"
include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "cin.mm"
include "co.mm"
include "csn.mm"
include "cima.mm"
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
include "adantr.mm"
include "isof1o.mm"
include "fpwwe2lem6.mm"
include "simp2d.mm"
include "f1ocnvfv2.mm"
include "simp3d.mm"
include "simp1d.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "isorel.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "adantrr.mm"
include "adantrl.mm"
include "breq12d.mm"
include "isocnv.mm"
include "ssbrd.mm"
include "imp.mm"
include "brxp.mm"
include "simplbi.mm"
include "3bitr4d.mm"
include "expr.mm"
include "jca.mm"

theorem fpwwe2lem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
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
  assert |- ( ( ph /\ C R ( M ` B ) ) -> ( C S ( N ` B ) /\ ( D R ( M ` B ) -> ( C R D <-> C S D ) ) ) )

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
    cB
    cN
    cfv
    #
    cS
    wbr
    cD
    @0
    cR
    wbr
    #
    cC
    cD
    cR
    wbr
    #
    cC
    cD
    cS
    wbr
    #
    wb
    #
    wi
    @2
    cC
    cN
    ccnv
    #
    cfv
    #
    cN
    cfv
    #
    cC
    @3
    cS
    @2
    cN
    cdm
    #
    cY
    cN
    wf1o
    #
    cC
    cY
    wcel
    #
    @10
    cC
    wceq
    @2
    @11
    cY
    cep
    cS
    cN
    wiso
    #
    @12
    wph
    @14
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
    @14
    wph
    cY
    cS
    cW
    wbr
    #
    @15
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
    @18
    @18
    cxp
    wss
    wa
    @18
    @19
    wwe
    vu
    cv
    #
    @19
    @20
    @20
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
    @19
    ccnv
    @22
    csn
    #
    cima
    wsbc
    vy
    @18
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
    @16
    @20
    cS
    @21
    cin
    cF
    co
    @22
    wceq
    vu
    cS
    ccnv
    @23
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
    @16
    @25
    wa
    #
    wph
    @17
    @26
    @27
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
    adantr
    #
    @11
    cY
    cep
    cS
    cN
    isof1o
    syl
    #
    @2
    cC
    cX
    wcel
    #
    @13
    cC
    cM
    ccnv
    #
    cfv
    #
    @9
    wceq
    #
    wph
    vx
    vy
    vu
    cA
    cB
    cC
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
    fpwwe2lem7.1
    fpwwe2lem7.2
    fpwwe2lem7.3
    fpwwe2lem6
    #
    simp2d
    #
    @11
    cY
    cC
    cN
    f1ocnvfv2
    syl2anc
    @2
    @9
    cB
    cep
    wbr
    #
    @10
    @3
    cS
    wbr
    #
    @2
    @33
    @9
    cB
    cep
    @2
    @31
    @13
    @34
    @35
    simp3d
    #
    @2
    @33
    cB
    cep
    wbr
    #
    @33
    cM
    cfv
    #
    @0
    cR
    wbr
    #
    @2
    @41
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
    @31
    @41
    cC
    wceq
    @2
    @43
    cX
    cep
    cR
    cM
    wiso
    #
    @44
    wph
    @45
    @1
    wph
    cX
    cvv
    wcel
    #
    cX
    cR
    wwe
    #
    @45
    wph
    cX
    cR
    cW
    wbr
    #
    @46
    fpwwe2lem9.x
    cX
    cR
    cW
    @24
    brrelexi
    syl
    wph
    @47
    @20
    cR
    @21
    cin
    cF
    co
    @22
    wceq
    vu
    cR
    ccnv
    @23
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
    @47
    @49
    wa
    #
    wph
    @48
    @53
    @54
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
    adantr
    #
    @43
    cX
    cep
    cR
    cM
    isof1o
    syl
    #
    @2
    @31
    @13
    @34
    @35
    simp1d
    #
    @43
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
    @45
    @33
    @43
    wcel
    cB
    @43
    wcel
    #
    @40
    @42
    wb
    @57
    @2
    cX
    @43
    cC
    @32
    @2
    @44
    cX
    @43
    @32
    wf1o
    cX
    @43
    @32
    wf
    @58
    @43
    cX
    cM
    f1ocnv
    cX
    @43
    @32
    f1of
    3syl
    @59
    ffvelrnd
    wph
    @60
    @1
    fpwwe2lem7.1
    adantr
    @43
    cX
    @33
    cB
    cep
    cR
    cM
    isorel
    syl12anc
    mpbird
    eqbrtrrd
    @2
    @14
    @9
    @11
    wcel
    cB
    @11
    wcel
    #
    @37
    @38
    wb
    @29
    @2
    cY
    @11
    cC
    @8
    @2
    @12
    cY
    @11
    @8
    wf1o
    cY
    @11
    @8
    wf
    @30
    @11
    cY
    cN
    f1ocnv
    cY
    @11
    @8
    f1of
    3syl
    @36
    ffvelrnd
    wph
    @61
    @1
    fpwwe2lem7.2
    adantr
    @11
    cY
    @9
    cB
    cep
    cS
    cN
    isorel
    syl12anc
    mpbid
    eqbrtrrd
    wph
    @1
    @4
    @7
    wph
    @1
    @4
    wa
    #
    wa
    #
    @33
    cD
    @32
    cfv
    #
    cep
    wbr
    #
    @9
    cD
    @8
    cfv
    #
    cep
    wbr
    #
    @5
    @6
    @63
    @33
    @9
    @64
    @66
    cep
    wph
    @1
    @34
    @4
    @39
    adantrr
    wph
    @4
    @64
    @66
    wceq
    #
    @1
    wph
    @4
    wa
    #
    cD
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    @68
    wph
    vx
    vy
    vu
    cA
    cB
    cD
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
    fpwwe2lem7.1
    fpwwe2lem7.2
    fpwwe2lem7.3
    fpwwe2lem6
    #
    simp3d
    adantrl
    breq12d
    @63
    cX
    @43
    cR
    cep
    @32
    wiso
    #
    @31
    @70
    @5
    @65
    wb
    @63
    @45
    @73
    wph
    @45
    @62
    @56
    adantr
    @43
    cX
    cep
    cR
    cM
    isocnv
    syl
    wph
    @1
    @31
    @4
    @59
    adantrr
    wph
    @4
    @70
    @1
    @69
    cD
    @0
    @51
    wbr
    #
    @70
    wph
    @4
    @74
    wph
    cR
    @51
    cD
    @0
    wph
    @50
    @52
    wph
    @53
    @54
    @55
    simpld
    simprd
    ssbrd
    imp
    @74
    @70
    @0
    cX
    wcel
    cD
    @0
    cX
    cX
    brxp
    simplbi
    syl
    adantrl
    cX
    @43
    cC
    cD
    cR
    cep
    @32
    isorel
    syl12anc
    @63
    cY
    @11
    cS
    cep
    @8
    wiso
    #
    @13
    @71
    @6
    @67
    wb
    @63
    @14
    @75
    wph
    @14
    @62
    @28
    adantr
    @11
    cY
    cep
    cS
    cN
    isocnv
    syl
    wph
    @1
    @13
    @4
    @36
    adantrr
    wph
    @4
    @71
    @1
    @69
    @70
    @71
    @68
    @72
    simp2d
    adantrl
    cY
    @11
    cC
    cD
    cS
    cep
    @8
    isorel
    syl12anc
    3bitr4d
    expr
    jca
end
