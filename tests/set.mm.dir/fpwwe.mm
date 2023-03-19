include "wbr.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "cop.mm"
include "df-ov.mm"
include "cvv.mm"
include "wfn.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "opex.mm"
include "fvco2.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cv.mm"
include "wss.mm"
include "cxp.mm"
include "wwe.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "bropaex12.mm"
include "op1stg.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "pm5.32i.mm"
include "copab.mm"
include "cin.mm"
include "wsbc.mm"
include "vex.mm"
include "cnvex.mm"
include "imaex.mm"
include "inex1.mm"
include "algrflem.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "sbcie.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "w3a.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "simp1.mm"
include "selpw.mm"
include "sylibr.mm"
include "wex.mm"
include "19.8a.mm"
include "3ad2ant3.mm"
include "ween.mm"
include "elind.mm"
include "sylan2.mm"
include "syl5eqel.mm"
include "fpwwe2.mm"
include "syl5bbr.mm"

theorem fpwwe
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let va: setvar a
  let vs: setvar s
  let vu: setvar u
  let vz: setvar z
  assume fpwwe.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) }
  assume fpwwe.2: |- ( ph -> A e. _V )
  assume fpwwe.3: |- ( ( ph /\ x e. ( ~P A i^i dom card ) ) -> ( F ` x ) e. A )
  assume fpwwe.4: |- X = U. dom W

  disjoint r x
  disjoint A r
  disjoint A x
  disjoint r y
  disjoint F r
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint Y r
  disjoint Y x
  disjoint Y y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint A a
  disjoint r s
  disjoint s x
  disjoint A s
  disjoint a u
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint r u
  disjoint r z
  disjoint s u
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint ph u
  disjoint R u
  disjoint X u
  disjoint Y u
  disjoint W u
  assert |- ( ph -> ( ( Y W R /\ ( F ` Y ) e. Y ) <-> ( Y = X /\ R = ( W ` X ) ) ) )

  proof
    cY
    cR
    cW
    wbr
    #
    cY
    cF
    cfv
    #
    cY
    wcel
    #
    wa
    @0
    cY
    cR
    cF
    c1st
    ccom
    #
    co
    #
    cY
    wcel
    #
    wa
    wph
    cY
    cX
    wceq
    cR
    cX
    cW
    cfv
    wceq
    wa
    @0
    @5
    @2
    @0
    @4
    @1
    cY
    @0
    @4
    cY
    cR
    cop
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @1
    @4
    @6
    @3
    cfv
    #
    @8
    cY
    cR
    @3
    df-ov
    c1st
    cvv
    wfn
    #
    @6
    cvv
    wcel
    @9
    @8
    wceq
    cvv
    cvv
    c1st
    wfo
    @10
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    cY
    cR
    opex
    cvv
    cF
    c1st
    @6
    fvco2
    mp2an
    eqtri
    @0
    @7
    cY
    cF
    @0
    cY
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    @7
    cY
    wceq
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
    wss
    #
    wa
    #
    @11
    @13
    wwe
    #
    @13
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    cF
    cfv
    #
    @18
    wceq
    #
    vy
    @11
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    cY
    cR
    cW
    fpwwe.1
    bropaex12
    cY
    cR
    cvv
    cvv
    op1stg
    syl
    fveq2d
    syl5eq
    eleq1d
    pm5.32i
    wph
    vx
    vy
    vu
    cA
    cR
    @3
    cW
    cX
    cY
    vr
    cW
    @25
    vx
    vr
    copab
    @15
    @16
    vu
    cv
    #
    @13
    @26
    @26
    cxp
    #
    cin
    #
    @3
    co
    #
    @18
    wceq
    #
    vu
    @20
    wsbc
    #
    vy
    @11
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    copab
    fpwwe.1
    @34
    @25
    vx
    vr
    @33
    @24
    @15
    @32
    @23
    @16
    @31
    @22
    vy
    @11
    @30
    @22
    vu
    @20
    @17
    @19
    @13
    vr
    vex
    #
    cnvex
    imaex
    @26
    @20
    wceq
    #
    @29
    @21
    @18
    @36
    @29
    @26
    cF
    cfv
    @21
    @26
    @28
    cF
    vu
    vex
    @13
    @27
    @35
    inex1
    algrflem
    @26
    @20
    cF
    fveq2
    syl5eq
    eqeq1d
    sbcie
    ralbii
    anbi2i
    anbi2i
    opabbii
    eqtr4i
    fpwwe.2
    wph
    @12
    @14
    @16
    w3a
    #
    wa
    @11
    @13
    @3
    co
    @11
    cF
    cfv
    #
    cA
    @11
    @13
    cF
    vx
    vex
    @35
    algrflem
    @37
    wph
    @11
    cA
    cpw
    #
    ccrd
    cdm
    #
    cin
    wcel
    @38
    cA
    wcel
    @37
    @39
    @40
    @11
    @37
    @12
    @11
    @39
    wcel
    @12
    @14
    @16
    simp1
    vx
    cA
    selpw
    sylibr
    @37
    @16
    vr
    wex
    #
    @11
    @40
    wcel
    @16
    @12
    @41
    @14
    @16
    vr
    19.8a
    3ad2ant3
    @11
    vr
    ween
    sylibr
    elind
    fpwwe.3
    sylan2
    syl5eqel
    fpwwe.4
    fpwwe2
    syl5bbr
end
