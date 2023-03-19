include "cfv.mm"
include "wcel.mm"
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
include "cvmsrcl.mm"
include "cpw.mm"
include "crab.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "fvmptss2.mm"
include "sseli.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "difeq1.mm"
include "raleqdv.mm"
include "anbi1d.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "eldifsn.mm"
include "elpwi.mm"
include "anim1i.mm"
include "syl.mm"
include "simprd.mm"
include "3jca.mm"

theorem cvmsi
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
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
  disjoint V k
  disjoint V s
  disjoint V t
  disjoint V u
  disjoint V v
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
  assert |- ( T e. ( S ` U ) -> ( U e. J /\ ( T C_ C /\ T =/= (/) ) /\ ( U. T = ( `' F " U ) /\ A. u e. T ( A. v e. ( T \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t U ) ) ) ) ) )

  proof
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
    @9
    csn
    #
    cdif
    #
    wral
    #
    cF
    @9
    cres
    #
    cC
    @9
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
    cvmsrcl
    @1
    cT
    cC
    cpw
    #
    wcel
    #
    @3
    wa
    #
    @4
    @1
    cT
    @22
    c0
    csn
    cdif
    #
    wcel
    #
    @24
    @1
    @26
    @21
    @1
    cT
    vs
    cv
    #
    cuni
    #
    @7
    wceq
    #
    @10
    vv
    @27
    @11
    cdif
    #
    wral
    #
    @18
    wa
    #
    vu
    @27
    wral
    #
    wa
    #
    vs
    @25
    crab
    #
    wcel
    @26
    @21
    wa
    @0
    @35
    cT
    vk
    cJ
    @28
    @6
    vk
    cv
    #
    cima
    #
    wceq
    #
    @31
    @14
    @15
    cJ
    @36
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
    @25
    crab
    @35
    cU
    cS
    @36
    cU
    wceq
    #
    @44
    @34
    vs
    @25
    @45
    @38
    @29
    @43
    @33
    @45
    @37
    @7
    @28
    @36
    cU
    @6
    imaeq2
    eqeq2d
    @45
    @42
    @32
    vu
    @27
    @45
    @41
    @18
    @31
    @45
    @40
    @17
    @14
    @45
    @39
    @16
    @15
    chmeo
    @36
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
    fvmptss2
    sseli
    @34
    @21
    vs
    cT
    @25
    @27
    cT
    wceq
    #
    @29
    @8
    @33
    @20
    @46
    @28
    @5
    @7
    @27
    cT
    unieq
    eqeq1d
    @32
    @19
    vu
    @27
    cT
    @46
    @31
    @13
    @18
    @46
    @10
    vv
    @30
    @12
    @27
    cT
    @11
    difeq1
    raleqdv
    anbi1d
    raleqbi1dv
    anbi12d
    elrab
    sylib
    #
    simpld
    cT
    @22
    c0
    eldifsn
    sylib
    @23
    @2
    @3
    cT
    cC
    elpwi
    anim1i
    syl
    @1
    @26
    @21
    @47
    simprd
    3jca
end
