include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "simpr2.mm"
include "simpr3.mm"
include "ccn.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cvmcn.mm"
include "adantr.mm"
include "eqid.mm"
include "cnf.mm"
include "ffn.mm"
include "elpreima.mm"
include "4syl.mm"
include "mpbir2and.mm"
include "simpr1.mm"
include "cvmsuni.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "inelcm.mm"
include "wo.mm"
include "cvmsdisj.mm"
include "3expb.mm"
include "sylan.mm"
include "ord.mm"
include "necon1ad.mm"
include "syl5.mm"
include "ralrimivva.mm"
include "eleq2.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem cvmseu
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
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
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  let cW: class W
  let cX: class X
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmseu.1: |- B = U. C

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
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint S x
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint B v
  disjoint B x
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
  disjoint P k
  disjoint P x
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
  disjoint U t
  disjoint U w
  disjoint U y
  disjoint U z
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
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( F e. ( C CovMap J ) /\ ( T e. ( S ` U ) /\ A e. B /\ ( F ` A ) e. U ) ) -> E! x e. T A e. x )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cT
    cU
    cS
    cfv
    wcel
    #
    cA
    cB
    wcel
    #
    cA
    cF
    cfv
    cU
    wcel
    #
    w3a
    #
    wa
    #
    cA
    vx
    cv
    #
    wcel
    #
    vx
    cT
    wrex
    #
    @7
    cA
    vz
    cv
    #
    wcel
    #
    wa
    #
    @6
    @9
    wceq
    #
    wi
    #
    vz
    cT
    wral
    vx
    cT
    wral
    @7
    vx
    cT
    wreu
    @5
    cA
    cT
    cuni
    #
    wcel
    @8
    @5
    cA
    cF
    ccnv
    cU
    cima
    #
    @14
    @5
    cA
    @15
    wcel
    #
    @2
    @3
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    @5
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    cB
    cJ
    cuni
    #
    cF
    wf
    cF
    cB
    wfn
    @16
    @2
    @3
    wa
    wb
    @0
    @17
    @4
    cC
    cF
    cJ
    cvmcn
    adantr
    cF
    cC
    cJ
    cB
    @18
    cvmseu.1
    @18
    eqid
    cnf
    cB
    @18
    cF
    ffn
    cB
    cA
    cU
    cF
    elpreima
    4syl
    mpbir2and
    @5
    @1
    @14
    @15
    wceq
    @0
    @1
    @2
    @3
    simpr1
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
    cvmsuni
    syl
    eleqtrrd
    vx
    cA
    cT
    eluni2
    sylib
    @5
    @13
    vx
    vz
    cT
    cT
    @11
    @6
    @9
    cin
    #
    c0
    wne
    @5
    @6
    cT
    wcel
    #
    @9
    cT
    wcel
    #
    wa
    #
    wa
    #
    @12
    cA
    @6
    @9
    inelcm
    @24
    @12
    @20
    c0
    @24
    @12
    @20
    c0
    wceq
    #
    @5
    @1
    @23
    @12
    @25
    wo
    #
    @19
    @1
    @21
    @22
    @26
    vv
    vu
    @6
    @9
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmsdisj
    3expb
    sylan
    ord
    necon1ad
    syl5
    ralrimivva
    @7
    @10
    vx
    vz
    cT
    @6
    @9
    cA
    eleq2
    reu4
    sylanbrc
end
