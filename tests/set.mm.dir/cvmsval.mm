include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "chmeo.mm"
include "w3a.mm"
include "cvmsi.mm"
include "3anass.mm"
include "cpw.mm"
include "crab.mm"
include "cvv.mm"
include "id.mm"
include "pwexg.mm"
include "difexg.mm"
include "rabexg.mm"
include "3syl.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "anbi1d.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "eldifsn.mm"
include "wb.mm"
include "elpw2g.mm"
include "adantr.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "biimprd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "impbid2.mm"

theorem cvmsval
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cW: class W
  let cX: class X
  let cA: class A
  let cB: class B
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )

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
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint V k
  disjoint V s
  disjoint V u
  disjoint V v
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b k
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U t
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint T x
  disjoint T z
  disjoint V a
  disjoint V b
  disjoint V t
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( C e. V -> ( T e. ( S ` U ) <-> ( U e. J /\ ( T C_ C /\ T =/= (/) ) /\ ( U. T = ( `' F " U ) /\ A. u e. T ( A. v e. ( T \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t U ) ) ) ) ) ) )

  proof
    cC
    cV
    wcel
    #
    cT
    cU
    cS
    cfv
    #
    wcel
    #
    cU
    cJ
    wcel
    #
    cT
    cC
    wss
    #
    cT
    c0
    wne
    #
    wa
    #
    cT
    cuni
    #
    cF
    ccnv
    #
    cU
    cima
    #
    wceq
    #
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    #
    vv
    cT
    @11
    csn
    #
    cdif
    #
    wral
    #
    cF
    @11
    cres
    #
    cC
    @11
    crest
    co
    #
    cJ
    cU
    crest
    co
    #
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vu
    cT
    wral
    #
    wa
    #
    w3a
    #
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
    cvmcov.1
    cvmsi
    @24
    @3
    @6
    @23
    wa
    #
    wa
    @0
    @2
    @3
    @6
    @23
    3anass
    @0
    @3
    @25
    @2
    @0
    @3
    wa
    #
    @2
    @25
    @26
    @2
    cT
    vs
    cv
    #
    cuni
    #
    @9
    wceq
    #
    @12
    vv
    @27
    @13
    cdif
    #
    wral
    #
    @20
    wa
    #
    vu
    @27
    wral
    #
    wa
    #
    vs
    cC
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    wcel
    #
    @25
    @26
    @1
    @38
    cT
    @3
    @3
    @38
    cvv
    wcel
    #
    @1
    @38
    wceq
    @0
    @3
    id
    @0
    @35
    cvv
    wcel
    @37
    cvv
    wcel
    @40
    cC
    cV
    pwexg
    @35
    @36
    cvv
    difexg
    @34
    vs
    @37
    cvv
    rabexg
    3syl
    vk
    cU
    @28
    @8
    vk
    cv
    #
    cima
    #
    wceq
    #
    @31
    @16
    @17
    cJ
    @41
    crest
    co
    #
    chmeo
    co
    #
    wcel
    #
    wa
    #
    vu
    @27
    wral
    #
    wa
    #
    vs
    @37
    crab
    @38
    cJ
    cvv
    cS
    @41
    cU
    wceq
    #
    @49
    @34
    vs
    @37
    @50
    @43
    @29
    @48
    @33
    @50
    @42
    @9
    @28
    @41
    cU
    @8
    imaeq2
    eqeq2d
    @50
    @47
    @32
    vu
    @27
    @50
    @46
    @20
    @31
    @50
    @45
    @19
    @16
    @50
    @44
    @18
    @17
    chmeo
    @41
    cU
    cJ
    crest
    oveq2
    oveq2d
    eleq2d
    anbi2d
    ralbidv
    anbi12d
    rabbidv
    cvmcov.1
    fvmptg
    syl2anr
    eleq2d
    @39
    cT
    @37
    wcel
    #
    @23
    wa
    @26
    @25
    @34
    @23
    vs
    cT
    @37
    @27
    cT
    wceq
    #
    @29
    @10
    @33
    @22
    @52
    @28
    @7
    @9
    @27
    cT
    unieq
    eqeq1d
    @32
    @21
    vu
    @27
    cT
    @52
    @31
    @15
    @20
    @52
    @12
    vv
    @30
    @14
    @27
    cT
    @13
    difeq1
    raleqdv
    anbi1d
    raleqbi1dv
    anbi12d
    elrab
    @26
    @51
    @6
    @23
    @51
    cT
    @35
    wcel
    #
    @5
    wa
    @26
    @6
    cT
    @35
    c0
    eldifsn
    @26
    @53
    @4
    @5
    @0
    @53
    @4
    wb
    @3
    cT
    cC
    cV
    elpw2g
    adantr
    anbi1d
    syl5bb
    anbi1d
    syl5bb
    bitrd
    biimprd
    expimpd
    syl5bi
    impbid2
end
