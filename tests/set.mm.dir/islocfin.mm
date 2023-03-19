include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "cuni.mm"
include "cab.mm"
include "df-locfin.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "cvv.mm"
include "cpw.mm"
include "wss.mm"
include "eqimss2.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "selpw.mm"
include "adantr.mm"
include "abssi.mm"
include "topopn.mm"
include "pwexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "rexeq.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "eleq2d.mm"
include "elex.mm"
include "adantl.mm"
include "simpr.mm"
include "syl6eq.mm"
include "eqeltrrd.mm"
include "syl.mm"
include "uniexb.mm"
include "adantrr.mm"
include "eqeq2d.mm"
include "rabeq.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "elabg.mm"
include "pm5.21nd.mm"
include "bitrd.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem islocfin
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vj: setvar j
  let vy: setvar y
  assume islocfin.1: |- X = U. J
  assume islocfin.2: |- Y = U. A

  disjoint n s
  disjoint n x
  disjoint A n
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint J n
  disjoint J x
  disjoint X x
  disjoint j n
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n y
  disjoint s y
  disjoint x y
  disjoint A y
  disjoint J j
  disjoint J y
  disjoint X j
  disjoint X y
  disjoint Y y
  assert |- ( A e. ( LocFin ` J ) <-> ( J e. Top /\ X = Y /\ A. x e. X E. n e. J ( x e. n /\ { s e. A | ( s i^i n ) =/= (/) } e. Fin ) ) )

  proof
    cA
    cJ
    clocfin
    cfv
    #
    wcel
    #
    cJ
    ctop
    wcel
    #
    cX
    cY
    wceq
    #
    vx
    cv
    vn
    cv
    #
    wcel
    #
    vs
    cv
    @4
    cin
    c0
    wne
    #
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    wa
    #
    wa
    @2
    @3
    @11
    w3a
    @1
    @2
    @12
    @1
    clocfin
    cdm
    ctop
    cJ
    vj
    ctop
    vj
    cv
    #
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @5
    @6
    vs
    @15
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    @13
    wrex
    #
    vx
    @14
    wral
    #
    wa
    #
    vy
    cab
    #
    clocfin
    vj
    vy
    vn
    vs
    vx
    df-locfin
    #
    dmmptss
    cA
    cJ
    clocfin
    elfvdm
    sseldi
    @2
    @1
    cA
    cX
    @16
    wceq
    #
    @20
    vn
    cJ
    wrex
    #
    vx
    cX
    wral
    #
    wa
    #
    vy
    cab
    #
    wcel
    #
    @12
    @2
    @0
    @30
    cA
    @2
    @30
    cvv
    wcel
    #
    @0
    @30
    wceq
    @2
    @30
    cX
    cpw
    #
    cpw
    #
    wss
    @34
    cvv
    wcel
    #
    @32
    @29
    vy
    @34
    @26
    @15
    @34
    wcel
    #
    @28
    @26
    @15
    @33
    wss
    #
    @36
    @26
    @16
    cX
    wss
    @37
    @16
    cX
    eqimss2
    @15
    cX
    sspwuni
    sylibr
    vy
    @33
    selpw
    sylibr
    adantr
    abssi
    @2
    cX
    cJ
    wcel
    #
    @33
    cvv
    wcel
    @35
    cJ
    cX
    islocfin.1
    topopn
    #
    cX
    cJ
    pwexg
    @33
    cvv
    pwexg
    3syl
    @30
    @34
    cvv
    ssexg
    sylancr
    vj
    cJ
    @24
    @30
    ctop
    cvv
    clocfin
    @13
    cJ
    wceq
    #
    @23
    @29
    vy
    @40
    @17
    @26
    @22
    @28
    @40
    @14
    cX
    @16
    @40
    @14
    cJ
    cuni
    cX
    @13
    cJ
    unieq
    islocfin.1
    syl6eqr
    #
    eqeq1d
    @40
    @21
    @27
    vx
    @14
    cX
    @41
    @20
    vn
    @13
    cJ
    rexeq
    raleqbidv
    anbi12d
    abbidv
    @25
    fvmptg
    mpdan
    eleq2d
    @2
    @31
    @12
    cA
    cvv
    wcel
    #
    @31
    @42
    @2
    cA
    @30
    elex
    adantl
    @2
    @3
    @42
    @11
    @2
    @3
    wa
    #
    cA
    cuni
    #
    cvv
    wcel
    #
    @42
    @43
    @44
    cJ
    wcel
    @45
    @43
    cX
    @44
    cJ
    @43
    cX
    cY
    @44
    @2
    @3
    simpr
    islocfin.2
    syl6eq
    @2
    @38
    @3
    @39
    adantr
    eqeltrrd
    @44
    cJ
    elex
    syl
    cA
    uniexb
    sylibr
    adantrr
    @29
    @12
    vy
    cA
    cvv
    @15
    cA
    wceq
    #
    @26
    @3
    @28
    @11
    @46
    @16
    cY
    cX
    @46
    @16
    @44
    cY
    @15
    cA
    unieq
    islocfin.2
    syl6eqr
    eqeq2d
    @46
    @27
    @10
    vx
    cX
    @46
    @20
    @9
    vn
    cJ
    @46
    @19
    @8
    @5
    @46
    @18
    @7
    cfn
    @6
    vs
    @15
    cA
    rabeq
    eleq1d
    anbi2d
    rexbidv
    ralbidv
    anbi12d
    elabg
    pm5.21nd
    bitrd
    biadan2
    @2
    @3
    @11
    3anass
    bitr4i
end
