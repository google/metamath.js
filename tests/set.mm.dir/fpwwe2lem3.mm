include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cxp.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "wss.mm"
include "wwe.mm"
include "wbr.mm"
include "fpwwe2lem2.mm"
include "mpbid.mm"
include "simprrd.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eqeq2.mm"
include "sbceqbid.mm"
include "rspccva.mm"
include "sylan.mm"
include "wb.mm"
include "cvv.mm"
include "cdm.mm"
include "cnvimass.mm"
include "relopabi.mm"
include "brrelex2i.mm"
include "dmexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "id.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "sbcieg.mm"
include "syl.mm"
include "adantr.mm"

theorem fpwwe2lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let vr: setvar r
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
  assume fpwwe2lem4.4: |- ( ph -> X W R )

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
  assert |- ( ( ph /\ B e. X ) -> ( ( `' R " { B } ) F ( R i^i ( ( `' R " { B } ) X. ( `' R " { B } ) ) ) ) = B )

  proof
    wph
    cB
    cX
    wcel
    #
    wa
    vu
    cv
    #
    cR
    @1
    @1
    cxp
    #
    cin
    #
    cF
    co
    #
    cB
    wceq
    #
    vu
    cR
    ccnv
    #
    cB
    csn
    #
    cima
    #
    wsbc
    #
    @8
    cR
    @8
    @8
    cxp
    #
    cin
    #
    cF
    co
    #
    cB
    wceq
    #
    wph
    @4
    vy
    cv
    #
    wceq
    #
    vu
    @6
    @14
    csn
    #
    cima
    #
    wsbc
    #
    vy
    cX
    wral
    #
    @0
    @9
    wph
    cX
    cA
    wss
    cR
    cX
    cX
    cxp
    wss
    wa
    #
    cX
    cR
    wwe
    #
    @19
    wph
    cX
    cR
    cW
    wbr
    #
    @20
    @21
    @19
    wa
    wa
    fpwwe2lem4.4
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
    simprrd
    @18
    @9
    vy
    cB
    cX
    @14
    cB
    wceq
    #
    @15
    @5
    vu
    @17
    @8
    @23
    @16
    @7
    @6
    @14
    cB
    sneq
    imaeq2d
    @14
    cB
    @4
    eqeq2
    sbceqbid
    rspccva
    sylan
    wph
    @9
    @13
    wb
    #
    @0
    wph
    @8
    cvv
    wcel
    #
    @24
    wph
    @8
    cR
    cdm
    #
    wss
    @26
    cvv
    wcel
    #
    @25
    cR
    @7
    cnvimass
    wph
    @22
    cR
    cvv
    wcel
    @27
    fpwwe2lem4.4
    cX
    cR
    cW
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @28
    @28
    cxp
    wss
    wa
    @28
    @29
    wwe
    @1
    @29
    @2
    cin
    cF
    co
    @14
    wceq
    vu
    @29
    ccnv
    @16
    cima
    wsbc
    vy
    @28
    wral
    wa
    wa
    vx
    vr
    cW
    fpwwe2.1
    relopabi
    brrelex2i
    cR
    cvv
    dmexg
    3syl
    @8
    @26
    cvv
    ssexg
    sylancr
    @5
    @13
    vu
    @8
    cvv
    @1
    @8
    wceq
    #
    @4
    @12
    cB
    @30
    @1
    @8
    @3
    @11
    cF
    @30
    id
    #
    @30
    @2
    @10
    cR
    @30
    @1
    @8
    @31
    sqxpeqd
    ineq2d
    oveq12d
    eqeq1d
    sbcieg
    syl
    adantr
    mpbid
end
