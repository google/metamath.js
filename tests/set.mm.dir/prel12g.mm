include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "cpr.mm"
include "wb.mm"
include "wi.mm"
include "weq.mm"
include "cv.mm"
include "eqeq1.mm"
include "notbid.mm"
include "preq1.mm"
include "eqeq1d.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "eqeq2.mm"
include "preq2.mm"
include "anbi2d.mm"
include "eqeq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "w3a.mm"
include "vex.mm"
include "prel12.mm"
include "vtoclg.mm"
include "a1i.mm"
include "vtocl3ga.mm"
include "3expa.mm"
include "impr.mm"

theorem prel12g
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


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( -. A = B -> ( { A , B } = { C , D } <-> ( A e. { C , D } /\ B e. { C , D } ) ) ) )

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
    wceq
    #
    wn
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
    @7
    wcel
    #
    cB
    @7
    wcel
    #
    wa
    #
    wb
    #
    wi
    #
    @0
    @1
    @2
    @3
    @13
    wi
    #
    @3
    vx
    vy
    weq
    #
    wn
    #
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
    @17
    @21
    wcel
    #
    @18
    @21
    wcel
    #
    wa
    #
    wb
    #
    wi
    #
    wi
    #
    @3
    cA
    @18
    wceq
    #
    wn
    #
    cA
    @18
    cpr
    #
    @21
    wceq
    #
    cA
    @21
    wcel
    #
    @24
    wa
    #
    wb
    #
    wi
    #
    wi
    @3
    @5
    @6
    @21
    wceq
    #
    @33
    cB
    @21
    wcel
    #
    wa
    #
    wb
    #
    wi
    #
    wi
    @14
    vx
    vy
    vz
    cA
    cB
    cC
    cV
    cW
    cX
    @17
    cA
    wceq
    #
    @27
    @36
    @3
    @42
    @16
    @30
    @26
    @35
    @42
    @15
    @29
    @17
    cA
    @18
    eqeq1
    notbid
    @42
    @22
    @32
    @25
    @34
    @42
    @19
    @31
    @21
    @17
    cA
    @18
    preq1
    eqeq1d
    @42
    @23
    @33
    @24
    @17
    cA
    @21
    eleq1
    anbi1d
    bibi12d
    imbi12d
    imbi2d
    @18
    cB
    wceq
    #
    @36
    @41
    @3
    @43
    @30
    @5
    @35
    @40
    @43
    @29
    @4
    @18
    cB
    cA
    eqeq2
    notbid
    @43
    @32
    @37
    @34
    @39
    @43
    @31
    @6
    @21
    @18
    cB
    cA
    preq2
    eqeq1d
    @43
    @24
    @38
    @33
    @18
    cB
    @21
    eleq1
    anbi2d
    bibi12d
    imbi12d
    imbi2d
    @20
    cC
    wceq
    #
    @41
    @13
    @3
    @44
    @40
    @12
    @5
    @44
    @37
    @8
    @39
    @11
    @44
    @21
    @7
    @6
    @20
    cC
    cD
    preq1
    #
    eqeq2d
    @44
    @33
    @9
    @38
    @10
    @44
    @21
    @7
    cA
    @45
    eleq2d
    @44
    @21
    @7
    cB
    @45
    eleq2d
    anbi12d
    bibi12d
    imbi2d
    imbi2d
    @28
    @17
    cV
    wcel
    @18
    cW
    wcel
    @20
    cX
    wcel
    w3a
    @16
    @19
    @20
    vw
    cv
    #
    cpr
    #
    wceq
    #
    @17
    @47
    wcel
    #
    @18
    @47
    wcel
    #
    wa
    #
    wb
    #
    wi
    @27
    vw
    cD
    cY
    @46
    cD
    wceq
    #
    @52
    @26
    @16
    @53
    @48
    @22
    @51
    @25
    @53
    @47
    @21
    @19
    @46
    cD
    @20
    preq2
    #
    eqeq2d
    @53
    @49
    @23
    @50
    @24
    @53
    @47
    @21
    @17
    @54
    eleq2d
    @53
    @47
    @21
    @18
    @54
    eleq2d
    anbi12d
    bibi12d
    imbi2d
    @17
    @18
    @20
    @46
    vx
    vex
    vy
    vex
    vz
    vex
    vw
    vex
    prel12
    vtoclg
    a1i
    vtocl3ga
    3expa
    impr
end
