include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "crest.mm"
include "ctopon.mm"
include "cres.mm"
include "chmeo.mm"
include "wf1o.mm"
include "cuni.mm"
include "wss.mm"
include "ctop.mm"
include "cvmtop1.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cvmsss.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "cvmtop2.mm"
include "cvmsrcl.mm"
include "cvmshmeo.mm"
include "3adant1.mm"
include "hmeof1o2.mm"
include "syl3anc.mm"

theorem cvmsf1o
  let vv: setvar v
  let vu: setvar u
  let cA: class A
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
  disjoint A u
  disjoint A v
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
  assert |- ( ( F e. ( C CovMap J ) /\ T e. ( S ` U ) /\ A e. T ) -> ( F |` A ) : A -1-1-onto-> U )

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
    cT
    wcel
    #
    w3a
    #
    cC
    cA
    crest
    co
    #
    cA
    ctopon
    cfv
    wcel
    #
    cJ
    cU
    crest
    co
    #
    cU
    ctopon
    cfv
    wcel
    #
    cF
    cA
    cres
    #
    @4
    @6
    chmeo
    co
    wcel
    #
    cA
    cU
    @8
    wf1o
    @3
    cC
    cC
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cA
    @10
    wss
    #
    @5
    @3
    cC
    ctop
    wcel
    #
    @11
    @0
    @1
    @13
    @2
    cC
    cF
    cJ
    cvmtop1
    3ad2ant1
    cC
    @10
    @10
    eqid
    toptopon
    sylib
    @3
    cA
    cC
    wcel
    @12
    @3
    cT
    cC
    cA
    @1
    @0
    cT
    cC
    wss
    @2
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
    cvmsss
    3ad2ant2
    @0
    @1
    @2
    simp3
    sseldd
    cA
    cC
    elssuni
    syl
    cA
    cC
    @10
    resttopon
    syl2anc
    @3
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cU
    @14
    wss
    #
    @7
    @3
    cJ
    ctop
    wcel
    #
    @15
    @0
    @1
    @17
    @2
    cC
    cF
    cJ
    cvmtop2
    3ad2ant1
    cJ
    @14
    @14
    eqid
    toptopon
    sylib
    @3
    cU
    cJ
    wcel
    #
    @16
    @1
    @0
    @18
    @2
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
    3ad2ant2
    cU
    cJ
    elssuni
    syl
    cU
    cJ
    @14
    resttopon
    syl2anc
    @1
    @2
    @9
    @0
    vv
    vu
    cA
    cC
    cS
    cT
    cU
    vk
    cF
    cJ
    vs
    cvmcov.1
    cvmshmeo
    3adant1
    @8
    @4
    @6
    cA
    cU
    hmeof1o2
    syl3anc
end
