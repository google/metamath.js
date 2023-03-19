include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cpw.mm"
include "wrex.mm"
include "cuni.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "elunii.mm"
include "syl2anc.mm"
include "eqid.mm"
include "cvmcov.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "mpbir.mm"
include "a1i.mm"
include "simprrl.mm"
include "adantr.mm"
include "elind.mm"
include "simprrr.mm"
include "wi.mm"
include "ctop.mm"
include "cvmtop2.mm"
include "syl.mm"
include "simprl.mm"
include "inopn.mm"
include "syl3anc.mm"
include "inss1.mm"
include "cvmsss2.mm"
include "mpd.mm"
include "wceq.mm"
include "eleq2.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"

theorem cvmcov2
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cP: class P
  let cS: class S
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
  let cT: class T
  let cV: class V
  let cW: class W
  let cX: class X
  let cA: class A
  let cB: class B
  assume cvmcov.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )

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
  disjoint U k
  disjoint U s
  disjoint U u
  disjoint U v
  disjoint U x
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
  disjoint U t
  disjoint U w
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
  assert |- ( ( F e. ( C CovMap J ) /\ U e. J /\ P e. U ) -> E. x e. ~P U ( P e. x /\ ( S ` x ) =/= (/) ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cU
    cJ
    wcel
    #
    cP
    cU
    wcel
    #
    w3a
    #
    cP
    vy
    cv
    #
    wcel
    #
    @4
    cS
    cfv
    c0
    wne
    #
    wa
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
    cU
    cpw
    #
    wrex
    #
    vy
    cJ
    @3
    @0
    cP
    cJ
    cuni
    #
    wcel
    #
    @7
    vy
    cJ
    wrex
    @0
    @1
    @2
    simp1
    #
    @3
    @2
    @1
    @16
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp2
    #
    cP
    cU
    cJ
    elunii
    syl2anc
    vy
    vv
    vu
    cC
    cP
    cS
    vk
    cF
    cJ
    @15
    vs
    cvmcov.1
    @15
    eqid
    cvmcov
    syl2anc
    @3
    @4
    cJ
    wcel
    #
    @7
    wa
    #
    wa
    #
    @4
    cU
    cin
    #
    @13
    wcel
    #
    cP
    @23
    wcel
    #
    @23
    cS
    cfv
    #
    c0
    wne
    #
    @14
    @24
    @22
    @24
    @23
    cU
    wss
    @4
    cU
    inss2
    @23
    cU
    @4
    cU
    vy
    vex
    inex1
    elpw
    mpbir
    a1i
    @22
    @4
    cU
    cP
    @3
    @20
    @5
    @6
    simprrl
    @3
    @2
    @21
    @18
    adantr
    elind
    @22
    @6
    @27
    @3
    @20
    @5
    @6
    simprrr
    @22
    @0
    @23
    cJ
    wcel
    #
    @23
    @4
    wss
    #
    @6
    @27
    wi
    @3
    @0
    @21
    @17
    adantr
    #
    @22
    cJ
    ctop
    wcel
    #
    @20
    @1
    @28
    @22
    @0
    @31
    @30
    cC
    cF
    cJ
    cvmtop2
    syl
    @3
    @20
    @7
    simprl
    @3
    @1
    @21
    @19
    adantr
    @4
    cU
    cJ
    inopn
    syl3anc
    @29
    @22
    @4
    cU
    inss1
    a1i
    vv
    vu
    cC
    cS
    @4
    vk
    cF
    cJ
    @23
    vs
    cvmcov.1
    cvmsss2
    syl3anc
    mpd
    @12
    @25
    @27
    wa
    vx
    @23
    @13
    @8
    @23
    wceq
    #
    @9
    @25
    @11
    @27
    @8
    @23
    cP
    eleq2
    @32
    @10
    @26
    c0
    @8
    @23
    cS
    fveq2
    neeq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
end
