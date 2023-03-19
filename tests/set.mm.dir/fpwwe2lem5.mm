include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "w3a.mm"
include "co.mm"
include "adantr.mm"
include "simpr1.mm"
include "ssexd.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "jca.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "sseq1.mm"
include "xpeq12.mm"
include "anidms.mm"
include "sseq2d.mm"
include "weeq2.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "weeq1.mm"
include "3anbi23d.mm"
include "oveq2.mm"
include "vtocl2g.mm"
include "mpcom.mm"

theorem fpwwe2lem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
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
  let cM: class M
  let cN: class N
  let cY: class Y
  let cS: class S
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume fpwwe2.2: |- ( ph -> A e. _V )
  assume fpwwe2.3: |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) -> ( x F r ) e. A )

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
  disjoint M r
  disjoint M u
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N r
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
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
  disjoint Y r
  disjoint Y u
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint S r
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint W a
  disjoint W b
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint W z
  assert |- ( ( ph /\ ( X C_ A /\ R C_ ( X X. X ) /\ R We X ) ) -> ( X F R ) e. A )

  proof
    cX
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
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
    cX
    cR
    wwe
    #
    w3a
    #
    wa
    #
    cX
    cR
    cF
    co
    #
    cA
    wcel
    #
    @7
    @0
    @1
    @7
    cX
    cA
    cvv
    wph
    cA
    cvv
    wcel
    @6
    fpwwe2.2
    adantr
    wph
    @2
    @4
    @5
    simpr1
    ssexd
    #
    @7
    cR
    @3
    cvv
    @7
    @0
    @0
    @3
    cvv
    wcel
    @10
    @10
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    wph
    @2
    @4
    @5
    simpr2
    ssexd
    jca
    wph
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @11
    @11
    cxp
    #
    wss
    #
    @11
    @13
    wwe
    #
    w3a
    #
    wa
    #
    @11
    @13
    cF
    co
    #
    cA
    wcel
    #
    wi
    wph
    @2
    @13
    @3
    wss
    #
    cX
    @13
    wwe
    #
    w3a
    #
    wa
    #
    cX
    @13
    cF
    co
    #
    cA
    wcel
    #
    wi
    @7
    @9
    wi
    vx
    vr
    cX
    cR
    cvv
    cvv
    @11
    cX
    wceq
    #
    @18
    @24
    @20
    @26
    @27
    @17
    @23
    wph
    @27
    @12
    @2
    @15
    @21
    @16
    @22
    @11
    cX
    cA
    sseq1
    @27
    @14
    @3
    @13
    @27
    @14
    @3
    wceq
    @11
    cX
    @11
    cX
    xpeq12
    anidms
    sseq2d
    @11
    cX
    @13
    weeq2
    3anbi123d
    anbi2d
    @27
    @19
    @25
    cA
    @11
    cX
    @13
    cF
    oveq1
    eleq1d
    imbi12d
    @13
    cR
    wceq
    #
    @24
    @7
    @26
    @9
    @28
    @23
    @6
    wph
    @28
    @21
    @4
    @22
    @5
    @2
    @13
    cR
    @3
    sseq1
    cX
    @13
    cR
    weeq1
    3anbi23d
    anbi2d
    @28
    @25
    @8
    cA
    @13
    cR
    cX
    cF
    oveq2
    eleq1d
    imbi12d
    fpwwe2.3
    vtocl2g
    mpcom
end
