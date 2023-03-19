include "cv.mm"
include "cmr.mm"
include "co.mm"
include "cm1r.mm"
include "cplr.mm"
include "cop.mm"
include "cmul.mm"
include "cnr.mm"
include "opex.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveqan12d.mm"
include "oveqan12rd.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "cc.mm"
include "wcel.mm"
include "wex.mm"
include "coprab.mm"
include "cxp.mm"
include "df-mul.mm"
include "df-c.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "oprabbii.mm"
include "eqtri.mm"
include "ov3.mm"

theorem mulcnsr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f


  assert |- ( ( ( A e. R. /\ B e. R. ) /\ ( C e. R. /\ D e. R. ) ) -> ( <. A , B >. x. <. C , D >. ) = <. ( ( A .R C ) +R ( -1R .R ( B .R D ) ) ) , ( ( B .R C ) +R ( A .R D ) ) >. )

  proof
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    vw
    cv
    #
    vu
    cv
    #
    cmr
    co
    #
    cm1r
    vv
    cv
    #
    vf
    cv
    #
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    @3
    @1
    cmr
    co
    #
    @0
    @4
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    cA
    cC
    cmr
    co
    #
    cm1r
    cB
    cD
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    cB
    cC
    cmr
    co
    #
    cA
    cD
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    vf
    cmul
    cnr
    @15
    @18
    opex
    @0
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    #
    @1
    cC
    wceq
    #
    @4
    cD
    wceq
    #
    wa
    #
    @11
    cA
    @1
    cmr
    co
    #
    cm1r
    cB
    @4
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    cB
    @1
    cmr
    co
    #
    cA
    @4
    cmr
    co
    #
    cplr
    co
    #
    cop
    @19
    @22
    @7
    @29
    @10
    @32
    @20
    @21
    @2
    @26
    @6
    @28
    cplr
    @0
    cA
    @1
    cmr
    oveq1
    @21
    @5
    @27
    cm1r
    cmr
    @3
    cB
    @4
    cmr
    oveq1
    oveq2d
    oveqan12d
    @21
    @20
    @8
    @30
    @9
    @31
    cplr
    @3
    cB
    @1
    cmr
    oveq1
    @0
    cA
    @4
    cmr
    oveq1
    oveqan12rd
    opeq12d
    @25
    @29
    @15
    @32
    @18
    @23
    @24
    @26
    @12
    @28
    @14
    cplr
    @1
    cC
    cA
    cmr
    oveq2
    @24
    @27
    @13
    cm1r
    cmr
    @4
    cD
    cB
    cmr
    oveq2
    oveq2d
    oveqan12d
    @23
    @24
    @30
    @16
    @31
    @17
    cplr
    @1
    cC
    cB
    cmr
    oveq2
    @4
    cD
    cA
    cmr
    oveq2
    oveqan12d
    opeq12d
    sylan9eq
    cmul
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    wa
    #
    @33
    @0
    @3
    cop
    wceq
    @35
    @1
    @4
    cop
    wceq
    wa
    vz
    cv
    @11
    wceq
    wa
    vf
    wex
    vu
    wex
    vv
    wex
    vw
    wex
    #
    wa
    #
    vx
    vy
    vz
    coprab
    @33
    cnr
    cnr
    cxp
    #
    wcel
    #
    @35
    @40
    wcel
    #
    wa
    #
    @38
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    vz
    vw
    vv
    vu
    vf
    df-mul
    @39
    @44
    vx
    vy
    vz
    @37
    @43
    @38
    @34
    @41
    @36
    @42
    cc
    @40
    @33
    df-c
    eleq2i
    cc
    @40
    @35
    df-c
    eleq2i
    anbi12i
    anbi1i
    oprabbii
    eqtri
    ov3
end
