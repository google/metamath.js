include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "copab.mm"
include "cpw.mm"
include "wcel.mm"
include "simpll.mm"
include "selpw.mm"
include "sylibr.mm"
include "simplr.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "jca.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "3sstr4i.mm"

theorem fpwwe2lem1
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cF: class F
  let cW: class W
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
  let cX: class X
  let cM: class M
  let cN: class N
  let wph: wff ph
  let cR: class R
  let cY: class Y
  let cS: class S
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }

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
  disjoint A r
  disjoint A x
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
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
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
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A a
  disjoint A s
  disjoint A t
  disjoint A w
  disjoint A z
  disjoint R r
  disjoint R u
  disjoint R w
  disjoint R x
  disjoint R y
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
  assert |- W C_ ( ~P A X. ~P ( A X. A ) )

  proof
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @0
    @0
    cxp
    #
    wss
    #
    wa
    @0
    @2
    wwe
    vu
    cv
    #
    @2
    @5
    @5
    cxp
    cin
    cF
    co
    vy
    cv
    #
    wceq
    vu
    @2
    ccnv
    @6
    csn
    cima
    wsbc
    vy
    @0
    wral
    wa
    #
    wa
    #
    vx
    vr
    copab
    @0
    cA
    cpw
    #
    wcel
    #
    @2
    cA
    cA
    cxp
    #
    cpw
    #
    wcel
    #
    wa
    #
    vx
    vr
    copab
    cW
    @9
    @12
    cxp
    @8
    @14
    vx
    vr
    @8
    @10
    @13
    @8
    @1
    @10
    @1
    @4
    @7
    simpll
    #
    vx
    cA
    selpw
    sylibr
    @8
    @2
    @11
    wss
    @13
    @8
    @2
    @3
    @11
    @1
    @4
    @7
    simplr
    @8
    @1
    @1
    @3
    @11
    wss
    @15
    @15
    @0
    cA
    @0
    cA
    xpss12
    syl2anc
    sstrd
    vr
    @11
    selpw
    sylibr
    jca
    ssopab2i
    fpwwe2.1
    vx
    vr
    @9
    @12
    df-xp
    3sstr4i
end
