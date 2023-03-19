include "coi.mm"
include "cdm.mm"
include "wss.mm"
include "wo.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "word.mm"
include "eqid.mm"
include "oicl.mm"
include "ordtri2or2.mm"
include "mp2an.mm"
include "cvv.mm"
include "wcel.mm"
include "adantr.mm"
include "cv.mm"
include "wwe.mm"
include "w3a.mm"
include "co.mm"
include "adantlr.mm"
include "wbr.mm"
include "simpr.mm"
include "fpwwe2lem9.mm"
include "ex.mm"
include "orim12d.mm"
include "mpi.mm"

theorem fpwwe2lem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
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
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume fpwwe2.2: |- ( ph -> A e. _V )
  assume fpwwe2.3: |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) -> ( x F r ) e. A )
  assume fpwwe2lem10.4: |- ( ph -> X W R )
  assume fpwwe2lem10.6: |- ( ph -> Y W S )

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
  assert |- ( ph -> ( ( X C_ Y /\ R = ( S i^i ( Y X. X ) ) ) \/ ( Y C_ X /\ S = ( R i^i ( X X. Y ) ) ) ) )

  proof
    wph
    cX
    cR
    coi
    #
    cdm
    #
    cY
    cS
    coi
    #
    cdm
    #
    wss
    #
    @3
    @1
    wss
    #
    wo
    #
    cX
    cY
    wss
    cR
    cS
    cY
    cX
    cxp
    cin
    wceq
    wa
    #
    cY
    cX
    wss
    cS
    cR
    cX
    cY
    cxp
    cin
    wceq
    wa
    #
    wo
    @1
    word
    @3
    word
    @6
    cX
    cR
    @0
    @0
    eqid
    #
    oicl
    cY
    cS
    @2
    @2
    eqid
    #
    oicl
    @1
    @3
    ordtri2or2
    mp2an
    wph
    @4
    @7
    @5
    @8
    wph
    @4
    @7
    wph
    @4
    wa
    vx
    vy
    vu
    cA
    cR
    cS
    cF
    @0
    @2
    cW
    cX
    cY
    vr
    fpwwe2.1
    wph
    cA
    cvv
    wcel
    #
    @4
    fpwwe2.2
    adantr
    wph
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @12
    @12
    cxp
    wss
    @12
    @13
    wwe
    w3a
    #
    @12
    @13
    cF
    co
    cA
    wcel
    #
    @4
    fpwwe2.3
    adantlr
    wph
    cX
    cR
    cW
    wbr
    #
    @4
    fpwwe2lem10.4
    adantr
    wph
    cY
    cS
    cW
    wbr
    #
    @4
    fpwwe2lem10.6
    adantr
    @9
    @10
    wph
    @4
    simpr
    fpwwe2lem9
    ex
    wph
    @5
    @8
    wph
    @5
    wa
    vx
    vy
    vu
    cA
    cS
    cR
    cF
    @2
    @0
    cW
    cY
    cX
    vr
    fpwwe2.1
    wph
    @11
    @5
    fpwwe2.2
    adantr
    wph
    @14
    @15
    @5
    fpwwe2.3
    adantlr
    wph
    @17
    @5
    fpwwe2lem10.6
    adantr
    wph
    @16
    @5
    fpwwe2lem10.4
    adantr
    @10
    @9
    wph
    @5
    simpr
    fpwwe2lem9
    ex
    orim12d
    mpi
end
