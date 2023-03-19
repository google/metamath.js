include "cv.mm"
include "cplr.mm"
include "co.mm"
include "cop.mm"
include "caddc.mm"
include "cnr.mm"
include "opex.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "opeq12.mm"
include "syl2an.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "cc.mm"
include "wcel.mm"
include "wex.mm"
include "coprab.mm"
include "cxp.mm"
include "df-add.mm"
include "df-c.mm"
include "eleq2i.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "oprabbii.mm"
include "eqtri.mm"
include "ov3.mm"

theorem addcnsr
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


  assert |- ( ( ( A e. R. /\ B e. R. ) /\ ( C e. R. /\ D e. R. ) ) -> ( <. A , B >. + <. C , D >. ) = <. ( A +R C ) , ( B +R D ) >. )

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
    cplr
    co
    #
    vv
    cv
    #
    vf
    cv
    #
    cplr
    co
    #
    cop
    #
    cA
    cC
    cplr
    co
    #
    cB
    cD
    cplr
    co
    #
    cop
    #
    vf
    caddc
    cnr
    @7
    @8
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
    @1
    cC
    wceq
    #
    @4
    cD
    wceq
    #
    wa
    @6
    cA
    @1
    cplr
    co
    #
    cB
    @4
    cplr
    co
    #
    cop
    #
    @9
    @10
    @2
    @14
    wceq
    @5
    @15
    wceq
    @6
    @16
    wceq
    @11
    @0
    cA
    @1
    cplr
    oveq1
    @3
    cB
    @4
    cplr
    oveq1
    @2
    @5
    @14
    @15
    opeq12
    syl2an
    @12
    @14
    @7
    wceq
    @15
    @8
    wceq
    @16
    @9
    wceq
    @13
    @1
    cC
    cA
    cplr
    oveq2
    @4
    cD
    cB
    cplr
    oveq2
    @14
    @15
    @7
    @8
    opeq12
    syl2an
    sylan9eq
    caddc
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
    @17
    @0
    @3
    cop
    wceq
    @19
    @1
    @4
    cop
    wceq
    wa
    vz
    cv
    @6
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
    @17
    cnr
    cnr
    cxp
    #
    wcel
    #
    @19
    @24
    wcel
    #
    wa
    #
    @22
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
    df-add
    @23
    @28
    vx
    vy
    vz
    @21
    @27
    @22
    @18
    @25
    @20
    @26
    cc
    @24
    @17
    df-c
    eleq2i
    cc
    @24
    @19
    df-c
    eleq2i
    anbi12i
    anbi1i
    oprabbii
    eqtri
    ov3
end
