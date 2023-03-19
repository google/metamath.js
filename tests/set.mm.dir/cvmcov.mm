include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wral.mm"
include "ctop.mm"
include "ccn.mm"
include "w3a.mm"
include "iscvm.mm"
include "simprbi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "mpan9.mm"
include "nfv.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "crest.mm"
include "chmeo.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfne.mm"
include "nfan.mm"
include "eleq2.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "cbvrex.mm"
include "sylibr.mm"

theorem cvmcov
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cP: class P
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cT: class T
  let cV: class V
  let cW: class W
  let cA: class A
  let cB: class B
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmcov.2: |- X = U. J

  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint C s
  disjoint u v
  disjoint u x
  disjoint C u
  disjoint v x
  disjoint C v
  disjoint C x
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint P k
  disjoint P x
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint S x
  disjoint X x
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
  disjoint k y
  disjoint k z
  disjoint s t
  disjoint s w
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
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint P y
  disjoint J a
  disjoint J b
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint S t
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint U k
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint T s
  disjoint T u
  disjoint T v
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
  assert |- ( ( F e. ( C CovMap J ) /\ P e. X ) -> E. x e. J ( P e. x /\ ( S ` x ) =/= (/) ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    cP
    vk
    cv
    #
    wcel
    #
    @2
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vk
    cJ
    wrex
    #
    cP
    vx
    cv
    #
    wcel
    #
    @8
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    vx
    cJ
    wrex
    @0
    @8
    @2
    wcel
    #
    @5
    wa
    #
    vk
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    @1
    @7
    @0
    cC
    ctop
    wcel
    cJ
    ctop
    wcel
    cF
    cC
    cJ
    ccn
    co
    wcel
    w3a
    @16
    vx
    vv
    vu
    cC
    cS
    vk
    cF
    cJ
    cX
    vs
    cvmcov.1
    cvmcov.2
    iscvm
    simprbi
    @15
    @7
    vx
    cP
    cX
    @8
    cP
    wceq
    #
    @14
    @6
    vk
    cJ
    @17
    @13
    @3
    @5
    @8
    cP
    @2
    eleq1
    anbi1d
    rexbidv
    rspcv
    mpan9
    @12
    @6
    vx
    vk
    cJ
    @9
    @11
    vk
    @9
    vk
    nfv
    vk
    @10
    c0
    vk
    @8
    cS
    vk
    cS
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    @2
    cima
    wceq
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @18
    @19
    csn
    cdif
    wral
    cF
    @19
    cres
    cC
    @19
    crest
    co
    cJ
    @2
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @18
    wral
    wa
    vs
    cC
    cpw
    c0
    csn
    cdif
    crab
    #
    cmpt
    cvmcov.1
    vk
    cJ
    @20
    nfmpt1
    nfcxfr
    vk
    @8
    nfcv
    nffv
    vk
    c0
    nfcv
    nfne
    nfan
    @6
    vx
    nfv
    @8
    @2
    wceq
    #
    @9
    @3
    @11
    @5
    @8
    @2
    cP
    eleq2
    @21
    @10
    @4
    c0
    @8
    @2
    cS
    fveq2
    neeq1d
    anbi12d
    cbvrex
    sylibr
end
