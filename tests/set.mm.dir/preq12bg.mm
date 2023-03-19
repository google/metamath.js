include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "wi.mm"
include "cv.mm"
include "weq.mm"
include "preq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "preq2.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "w3a.mm"
include "vex.mm"
include "preq12b.mm"
include "vtoclbg.mm"
include "a1i.mm"
include "vtocl3ga.mm"
include "3expa.mm"
include "impr.mm"

theorem preq12bg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cC
    cX
    wcel
    #
    cD
    cY
    wcel
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    #
    cA
    cD
    wceq
    #
    cB
    cC
    wceq
    #
    wa
    #
    wo
    #
    wb
    #
    @0
    @1
    @2
    @3
    @14
    wi
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    vz
    cv
    #
    cD
    cpr
    #
    wceq
    #
    vx
    vz
    weq
    #
    @17
    cD
    wceq
    #
    wa
    #
    @16
    cD
    wceq
    #
    vy
    vz
    weq
    #
    wa
    #
    wo
    #
    wb
    #
    wi
    #
    @3
    cA
    @17
    cpr
    #
    @20
    wceq
    #
    cA
    @19
    wceq
    #
    @23
    wa
    #
    @10
    @26
    wa
    #
    wo
    #
    wb
    #
    wi
    @3
    @4
    @20
    wceq
    #
    @33
    @8
    wa
    #
    @10
    cB
    @19
    wceq
    #
    wa
    #
    wo
    #
    wb
    #
    wi
    @15
    vx
    vy
    vz
    cA
    cB
    cC
    cV
    cW
    cX
    @16
    cA
    wceq
    #
    @29
    @37
    @3
    @44
    @21
    @32
    @28
    @36
    @44
    @18
    @31
    @20
    @16
    cA
    @17
    preq1
    eqeq1d
    @44
    @24
    @34
    @27
    @35
    @44
    @22
    @33
    @23
    @16
    cA
    @19
    eqeq1
    anbi1d
    @44
    @25
    @10
    @26
    @16
    cA
    cD
    eqeq1
    anbi1d
    orbi12d
    bibi12d
    imbi2d
    @17
    cB
    wceq
    #
    @37
    @43
    @3
    @45
    @32
    @38
    @36
    @42
    @45
    @31
    @4
    @20
    @17
    cB
    cA
    preq2
    eqeq1d
    @45
    @34
    @39
    @35
    @41
    @45
    @23
    @8
    @33
    @17
    cB
    cD
    eqeq1
    anbi2d
    @45
    @26
    @40
    @10
    @17
    cB
    @19
    eqeq1
    anbi2d
    orbi12d
    bibi12d
    imbi2d
    @19
    cC
    wceq
    #
    @43
    @14
    @3
    @46
    @38
    @6
    @42
    @13
    @46
    @20
    @5
    @4
    @19
    cC
    cD
    preq1
    eqeq2d
    @46
    @39
    @9
    @41
    @12
    @46
    @33
    @7
    @8
    @19
    cC
    cA
    eqeq2
    anbi1d
    @46
    @40
    @11
    @10
    @19
    cC
    cB
    eqeq2
    anbi2d
    orbi12d
    bibi12d
    imbi2d
    @30
    @16
    cV
    wcel
    @17
    cW
    wcel
    @19
    cX
    wcel
    w3a
    @18
    @19
    vw
    cv
    #
    cpr
    #
    wceq
    @22
    vy
    vw
    weq
    #
    wa
    #
    vx
    vw
    weq
    #
    @26
    wa
    #
    wo
    @21
    @28
    vw
    cD
    cY
    @47
    cD
    wceq
    #
    @48
    @20
    @18
    @47
    cD
    @19
    preq2
    eqeq2d
    @53
    @50
    @24
    @52
    @27
    @53
    @49
    @23
    @22
    @47
    cD
    @17
    eqeq2
    anbi2d
    @53
    @51
    @25
    @26
    @47
    cD
    @16
    eqeq2
    anbi1d
    orbi12d
    @16
    @17
    @19
    @47
    vx
    vex
    vy
    vex
    vz
    vex
    vw
    vex
    preq12b
    vtoclbg
    a1i
    vtocl3ga
    3expa
    impr
end
