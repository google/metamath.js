include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cdif.mm"
include "cpw.mm"
include "crab.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "selpw.mm"
include "anbi1i.mm"
include "bitri.mm"
include "a1i.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "wsbc.mm"
include "c0.mm"
include "ssdif0.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sylbi.mm"
include "sbcieg.mm"
include "biimpar.mm"
include "sylan2.mm"
include "3adant3.mm"
include "0ex.mm"
include "sbcie.mm"
include "dif0.mm"
include "eleq1i.mm"
include "sylbb.mm"
include "con3i.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "sscon.mm"
include "ssfi.mm"
include "expcom.mm"
include "syl.mm"
include "vex.mm"
include "3imtr4g.mm"
include "cin.mm"
include "cun.mm"
include "difindi.mm"
include "unfi.mm"
include "syl5eqel.mm"
include "anbi12i.mm"
include "inex1.mm"
include "isfild.mm"

theorem cfinfil
  let vx: setvar x
  let cA: class A
  let cV: class V
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( X e. V /\ A C_ X /\ -. A e. Fin ) -> { x e. ~P X | ( A \ x ) e. Fin } e. ( Fil ` X ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cX
    wss
    #
    cA
    cfn
    wcel
    #
    wn
    #
    w3a
    #
    cA
    vy
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    vy
    vz
    vw
    cX
    cA
    vx
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    @5
    @12
    wcel
    #
    @5
    cX
    wss
    #
    @7
    wa
    #
    wb
    @4
    @13
    @5
    @11
    wcel
    #
    @7
    wa
    @15
    @10
    @7
    vx
    @5
    @11
    @8
    @5
    wceq
    @9
    @6
    cfn
    @8
    @5
    cA
    difeq2
    eleq1d
    elrab
    @16
    @14
    @7
    vy
    cX
    selpw
    anbi1i
    bitri
    a1i
    @0
    @1
    cX
    cvv
    wcel
    @3
    cX
    cV
    elex
    3ad2ant1
    @0
    @1
    @7
    vy
    cX
    wsbc
    #
    @3
    @1
    @0
    cA
    cX
    cdif
    #
    cfn
    wcel
    #
    @17
    @1
    @18
    c0
    wceq
    #
    @19
    cA
    cX
    ssdif0
    @20
    @19
    c0
    cfn
    wcel
    0fin
    @18
    c0
    cfn
    eleq1
    mpbiri
    sylbi
    @0
    @17
    @19
    @7
    @19
    vy
    cX
    cV
    @5
    cX
    wceq
    @6
    @18
    cfn
    @5
    cX
    cA
    difeq2
    eleq1d
    sbcieg
    biimpar
    sylan2
    3adant3
    @3
    @0
    @7
    vy
    c0
    wsbc
    #
    wn
    @1
    @21
    @2
    @21
    cA
    c0
    cdif
    #
    cfn
    wcel
    #
    @2
    @7
    @23
    vy
    c0
    0ex
    @5
    c0
    wceq
    @6
    @22
    cfn
    @5
    c0
    cA
    difeq2
    eleq1d
    sbcie
    @22
    cA
    cfn
    cA
    dif0
    eleq1i
    sylbb
    con3i
    3ad2ant3
    vw
    cv
    #
    vz
    cv
    #
    wss
    #
    @4
    @7
    vy
    @24
    wsbc
    #
    @7
    vy
    @25
    wsbc
    #
    wi
    @25
    cX
    wss
    #
    @26
    cA
    @24
    cdif
    #
    cfn
    wcel
    #
    cA
    @25
    cdif
    #
    cfn
    wcel
    #
    @27
    @28
    @26
    @32
    @30
    wss
    #
    @31
    @33
    wi
    @24
    @25
    cA
    sscon
    @31
    @34
    @33
    @30
    @32
    ssfi
    expcom
    syl
    @7
    @31
    vy
    @24
    vw
    vex
    @5
    @24
    wceq
    @6
    @30
    cfn
    @5
    @24
    cA
    difeq2
    eleq1d
    sbcie
    #
    @7
    @33
    vy
    @25
    vz
    vex
    #
    @5
    @25
    wceq
    @6
    @32
    cfn
    @5
    @25
    cA
    difeq2
    eleq1d
    sbcie
    #
    3imtr4g
    3ad2ant3
    @4
    @29
    @24
    cX
    wss
    w3a
    #
    @33
    @31
    wa
    #
    cA
    @25
    @24
    cin
    #
    cdif
    #
    cfn
    wcel
    #
    @28
    @27
    wa
    @7
    vy
    @40
    wsbc
    @39
    @42
    wi
    @38
    @39
    @41
    @32
    @30
    cun
    cfn
    cA
    @25
    @24
    difindi
    @32
    @30
    unfi
    syl5eqel
    a1i
    @28
    @33
    @27
    @31
    @37
    @35
    anbi12i
    @7
    @42
    vy
    @40
    @25
    @24
    @36
    inex1
    @5
    @40
    wceq
    @6
    @41
    cfn
    @5
    @40
    cA
    difeq2
    eleq1d
    sbcie
    3imtr4g
    isfild
end
