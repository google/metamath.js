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
include "weq.mm"
include "simpl.mm"
include "sseq1d.mm"
include "simpr.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "id.mm"
include "ineq2d.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "cbvsbcv.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "eqeq2.mm"
include "sbceqbid.mm"
include "syl5bb.mm"
include "cbvralv.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "ineq1d.mm"
include "oveq2d.mm"
include "raleqbidv.mm"
include "cbvopabv.mm"
include "eqtri.mm"

theorem fpwwe2cbv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cF: class F
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let cB: class B
  let vb: setvar b
  let vt: setvar t
  let vw: setvar w
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
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint A a
  disjoint A r
  disjoint A s
  disjoint A x
  disjoint A z
  disjoint B u
  disjoint B y
  disjoint a b
  disjoint a t
  disjoint a w
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
  disjoint r t
  disjoint r w
  disjoint s t
  disjoint s w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
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
  disjoint A t
  disjoint A w
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
  assert |- W = { <. a , s >. | ( ( a C_ A /\ s C_ ( a X. a ) ) /\ ( s We a /\ A. z e. a [. ( `' s " { z } ) / v ]. ( v F ( s i^i ( v X. v ) ) ) = z ) ) }

  proof
    cW
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
    #
    @0
    @2
    wwe
    #
    vu
    cv
    #
    @2
    @7
    @7
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
    @2
    ccnv
    #
    @11
    csn
    #
    cima
    #
    wsbc
    #
    vy
    @0
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    copab
    va
    cv
    #
    cA
    wss
    #
    vs
    cv
    #
    @20
    @20
    cxp
    #
    wss
    #
    wa
    #
    @20
    @22
    wwe
    #
    vv
    cv
    #
    @22
    @27
    @27
    cxp
    #
    cin
    #
    cF
    co
    #
    vz
    cv
    #
    wceq
    #
    vv
    @22
    ccnv
    #
    @31
    csn
    #
    cima
    #
    wsbc
    #
    vz
    @20
    wral
    #
    wa
    #
    wa
    #
    va
    vs
    copab
    fpwwe2.1
    @19
    @39
    vx
    vr
    va
    vs
    vx
    va
    weq
    #
    vr
    vs
    weq
    #
    wa
    #
    @5
    @25
    @18
    @38
    @42
    @1
    @21
    @4
    @24
    @42
    @0
    @20
    cA
    @40
    @41
    simpl
    #
    sseq1d
    @42
    @2
    @22
    @3
    @23
    @40
    @41
    simpr
    #
    @42
    @0
    @20
    @43
    sqxpeqd
    sseq12d
    anbi12d
    @42
    @6
    @26
    @17
    @37
    @40
    @6
    @20
    @2
    wwe
    @41
    @26
    @0
    @20
    @2
    weeq2
    @20
    @2
    @22
    weeq1
    sylan9bb
    @17
    @27
    @2
    @28
    cin
    #
    cF
    co
    #
    @31
    wceq
    #
    vv
    @13
    @34
    cima
    #
    wsbc
    #
    vz
    @0
    wral
    @42
    @37
    @16
    @49
    vy
    vz
    @0
    @16
    @46
    @11
    wceq
    #
    vv
    @15
    wsbc
    vy
    vz
    weq
    #
    @49
    @12
    @50
    vu
    vv
    @15
    vu
    vv
    weq
    #
    @10
    @46
    @11
    @52
    @7
    @27
    @9
    @45
    cF
    @52
    id
    #
    @52
    @8
    @28
    @2
    @52
    @7
    @27
    @53
    sqxpeqd
    ineq2d
    oveq12d
    eqeq1d
    cbvsbcv
    @51
    @50
    @47
    vv
    @15
    @48
    @51
    @14
    @34
    @13
    @11
    @31
    sneq
    imaeq2d
    @11
    @31
    @46
    eqeq2
    sbceqbid
    syl5bb
    cbvralv
    @42
    @49
    @36
    vz
    @0
    @20
    @43
    @42
    @47
    @32
    vv
    @48
    @35
    @42
    @13
    @33
    @34
    @42
    @2
    @22
    @44
    cnveqd
    imaeq1d
    @42
    @46
    @30
    @31
    @42
    @45
    @29
    @27
    cF
    @42
    @2
    @22
    @28
    @44
    ineq1d
    oveq2d
    eqeq1d
    sbceqbid
    raleqbidv
    syl5bb
    anbi12d
    anbi12d
    cbvopabv
    eqtri
end
