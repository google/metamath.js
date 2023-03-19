include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "con0.mm"
include "wrex.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "csuc.mm"
include "wa.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "cvv.mm"
include "crab.mm"
include "cint.mm"
include "funmpt2.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "rabn0.mm"
include "sylibr.mm"
include "intex.mm"
include "sylib.mm"
include "vex.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "eleq1d.mm"
include "dmmpt.mm"
include "elrab2.mm"
include "mpbiran.mm"
include "funfvima.mm"
include "sylancr.mm"
include "tz9.12lem2.mm"
include "tz9.12lem1.mm"
include "onsucuni.mm"
include "ax-mp.mm"
include "sseli.mm"
include "r1ord2.mm"
include "mpsyl.mm"
include "syl6.mm"
include "imp.mm"
include "fvmptg.mm"
include "mpan.mm"
include "sylbi.mm"
include "ssrab2.mm"
include "onint.mm"
include "eqeltrd.mm"
include "cbvrabv.mm"
include "simprbi.mm"
include "3syl.mm"
include "adantr.mm"
include "sseldd.mm"
include "exp31.mm"
include "com3r.mm"
include "rexlimdv.mm"
include "ralimia.mm"
include "cpw.mm"
include "r1suc.mm"
include "eleq2i.mm"
include "elpw.mm"
include "dfss3.mm"
include "3bitri.mm"

theorem tz9.12lem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cF: class F
  assume tz9.12lem.1: |- A e. _V
  assume tz9.12lem.2: |- F = ( z e. _V |-> |^| { v e. On | z e. ( R1 ` v ) } )

  disjoint x y
  disjoint x z
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint v y
  disjoint A y
  disjoint v z
  disjoint A z
  disjoint A v
  disjoint F x
  disjoint F y
  assert |- ( A. x e. A E. y e. On x e. ( R1 ` y ) -> A e. ( R1 ` suc suc U. ( F " A ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cr1
    cfv
    #
    wcel
    #
    vy
    con0
    wrex
    #
    vx
    cA
    wral
    @0
    cF
    cA
    cima
    #
    cuni
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    cA
    @6
    csuc
    cr1
    cfv
    #
    wcel
    #
    @4
    @8
    vx
    cA
    @0
    cA
    wcel
    #
    @3
    @8
    vy
    con0
    @1
    con0
    wcel
    #
    @3
    @12
    @8
    @13
    @3
    @12
    @8
    @13
    @3
    wa
    #
    @12
    wa
    @0
    cF
    cfv
    #
    cr1
    cfv
    #
    @7
    @0
    @14
    @12
    @16
    @7
    wss
    #
    @14
    @12
    @15
    @5
    wcel
    #
    @17
    @14
    cF
    wfun
    @0
    cF
    cdm
    #
    wcel
    #
    @12
    @18
    wi
    vz
    cvv
    vz
    cv
    #
    vv
    cv
    #
    cr1
    cfv
    #
    wcel
    #
    vv
    con0
    crab
    #
    cint
    #
    cF
    tz9.12lem.2
    funmpt2
    @14
    @0
    @23
    wcel
    #
    vv
    con0
    crab
    #
    cint
    #
    cvv
    wcel
    #
    @20
    @14
    @28
    c0
    wne
    #
    @30
    @14
    @27
    vv
    con0
    wrex
    @31
    @27
    @3
    vv
    @1
    con0
    @22
    @1
    wceq
    @23
    @2
    @0
    @22
    @1
    cr1
    fveq2
    eleq2d
    #
    rspcev
    @27
    vv
    con0
    rabn0
    sylibr
    #
    @28
    intex
    #
    sylib
    @20
    @0
    cvv
    wcel
    #
    @30
    vx
    vex
    #
    @26
    cvv
    wcel
    @30
    vz
    @0
    cvv
    @19
    @21
    @0
    wceq
    #
    @26
    @29
    cvv
    @37
    @25
    @28
    @37
    @24
    @27
    vv
    con0
    @21
    @0
    @23
    eleq1
    rabbidv
    inteqd
    #
    eleq1d
    vz
    cvv
    @26
    cF
    tz9.12lem.2
    dmmpt
    elrab2
    mpbiran
    sylibr
    cA
    @0
    cF
    funfvima
    sylancr
    @6
    con0
    wcel
    #
    @18
    @15
    @6
    wcel
    @17
    vz
    vv
    cA
    cF
    tz9.12lem.1
    tz9.12lem.2
    tz9.12lem2
    #
    @5
    @6
    @15
    @5
    con0
    wss
    @5
    @6
    wss
    vz
    vv
    cA
    cF
    tz9.12lem.1
    tz9.12lem.2
    tz9.12lem1
    @5
    onsucuni
    ax-mp
    sseli
    @15
    @6
    r1ord2
    mpsyl
    syl6
    imp
    @14
    @0
    @16
    wcel
    #
    @12
    @14
    @31
    @15
    @28
    wcel
    #
    @41
    @33
    @31
    @15
    @29
    @28
    @31
    @30
    @15
    @29
    wceq
    #
    @34
    @35
    @30
    @43
    @36
    vz
    @0
    @26
    @29
    cvv
    cvv
    cF
    @38
    tz9.12lem.2
    fvmptg
    mpan
    sylbi
    @28
    con0
    wss
    @31
    @29
    @28
    wcel
    @27
    vv
    con0
    ssrab2
    @28
    onint
    mpan
    eqeltrd
    @42
    @15
    con0
    wcel
    @41
    @3
    @41
    vy
    @15
    con0
    @28
    @1
    @15
    wceq
    @2
    @16
    @0
    @1
    @15
    cr1
    fveq2
    eleq2d
    @27
    @3
    vv
    vy
    con0
    @32
    cbvrabv
    elrab2
    simprbi
    3syl
    adantr
    sseldd
    exp31
    com3r
    rexlimdv
    ralimia
    @11
    cA
    @7
    cpw
    #
    wcel
    cA
    @7
    wss
    @9
    @10
    @44
    cA
    @39
    @10
    @44
    wceq
    @40
    @6
    r1suc
    ax-mp
    eleq2i
    cA
    @7
    tz9.12lem.1
    elpw
    vx
    cA
    @7
    dfss3
    3bitri
    sylibr
end
