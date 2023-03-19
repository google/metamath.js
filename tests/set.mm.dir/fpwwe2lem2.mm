include "wbr.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "cv.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "relopabi.mm"
include "a1i.mm"
include "brrelex12.mm"
include "sylan.mm"
include "adantr.mm"
include "simprll.mm"
include "ssexd.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simprlr.mm"
include "jca.mm"
include "simpl.mm"
include "sseq1d.mm"
include "simpr.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ineq1d.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "sbceqbid.mm"
include "raleqbidv.mm"
include "brabga.mm"
include "pm5.21nd.mm"

theorem fpwwe2lem2
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
  assert |- ( ph -> ( X W R <-> ( ( X C_ A /\ R C_ ( X X. X ) ) /\ ( R We X /\ A. y e. X [. ( `' R " { y } ) / u ]. ( u F ( R i^i ( u X. u ) ) ) = y ) ) ) )

  proof
    wph
    cX
    cR
    cW
    wbr
    #
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
    wa
    #
    cX
    cR
    wwe
    #
    vu
    cv
    #
    cR
    @6
    @6
    cxp
    #
    cin
    #
    cF
    co
    #
    vy
    cv
    #
    wceq
    #
    vu
    cR
    ccnv
    #
    @10
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
    wa
    #
    wa
    #
    cX
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    wph
    cW
    wrel
    #
    @0
    @21
    @22
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
    @23
    @23
    cxp
    #
    wss
    #
    wa
    #
    @23
    @25
    wwe
    #
    @6
    @25
    @7
    cin
    #
    cF
    co
    #
    @10
    wceq
    #
    vu
    @25
    ccnv
    #
    @13
    cima
    #
    wsbc
    #
    vy
    @23
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    cW
    fpwwe2.1
    relopabi
    a1i
    cX
    cR
    cW
    brrelex12
    sylan
    wph
    @18
    wa
    #
    @19
    @20
    @39
    cX
    cA
    cvv
    wph
    cA
    cvv
    wcel
    @18
    fpwwe2.2
    adantr
    wph
    @1
    @3
    @17
    simprll
    ssexd
    #
    @39
    cR
    @2
    cvv
    @39
    @19
    @19
    @2
    cvv
    wcel
    @40
    @40
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    wph
    @1
    @3
    @17
    simprlr
    ssexd
    jca
    @38
    @18
    vx
    vr
    cX
    cR
    cW
    cvv
    cvv
    @23
    cX
    wceq
    #
    @25
    cR
    wceq
    #
    wa
    #
    @28
    @4
    @37
    @17
    @43
    @24
    @1
    @27
    @3
    @43
    @23
    cX
    cA
    @41
    @42
    simpl
    #
    sseq1d
    @43
    @25
    cR
    @26
    @2
    @41
    @42
    simpr
    #
    @43
    @23
    cX
    @44
    sqxpeqd
    sseq12d
    anbi12d
    @43
    @29
    @5
    @36
    @16
    @41
    @29
    cX
    @25
    wwe
    @42
    @5
    @23
    cX
    @25
    weeq2
    cX
    @25
    cR
    weeq1
    sylan9bb
    @43
    @35
    @15
    vy
    @23
    cX
    @44
    @43
    @32
    @11
    vu
    @34
    @14
    @43
    @33
    @12
    @13
    @43
    @25
    cR
    @45
    cnveqd
    imaeq1d
    @43
    @31
    @9
    @10
    @43
    @30
    @8
    @6
    cF
    @43
    @25
    cR
    @7
    @45
    ineq1d
    oveq2d
    eqeq1d
    sbceqbid
    raleqbidv
    anbi12d
    anbi12d
    fpwwe2.1
    brabga
    pm5.21nd
end
