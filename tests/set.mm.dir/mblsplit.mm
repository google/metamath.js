include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wi.mm"
include "reex.mm"
include "elpw2.mm"
include "cv.mm"
include "wral.mm"
include "ismbl.mm"
include "simprbi.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "difeq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl.mm"
include "syl5bir.mm"
include "3imp.mm"

theorem mblsplit
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. dom vol /\ B C_ RR /\ ( vol* ` B ) e. RR ) -> ( vol* ` B ) = ( ( vol* ` ( B i^i A ) ) + ( vol* ` ( B \ A ) ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    #
    cB
    cr
    wss
    #
    cB
    covol
    cfv
    #
    cr
    wcel
    #
    @2
    cB
    cA
    cin
    #
    covol
    cfv
    #
    cB
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @1
    cB
    cr
    cpw
    #
    wcel
    #
    @0
    @3
    @9
    wi
    #
    cB
    cr
    reex
    elpw2
    @0
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @14
    @13
    cA
    cin
    #
    covol
    cfv
    #
    @13
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vx
    @10
    wral
    #
    @11
    @12
    wi
    @0
    cA
    cr
    wss
    @23
    vx
    cA
    ismbl
    simprbi
    @22
    @12
    vx
    cB
    @10
    @13
    cB
    wceq
    #
    @15
    @3
    @21
    @9
    @24
    @14
    @2
    cr
    @13
    cB
    covol
    fveq2
    #
    eleq1d
    @24
    @14
    @2
    @20
    @8
    @25
    @24
    @17
    @5
    @19
    @7
    caddc
    @24
    @16
    @4
    covol
    @13
    cB
    cA
    ineq1
    fveq2d
    @24
    @18
    @6
    covol
    @13
    cB
    cA
    difeq1
    fveq2d
    oveq12d
    eqeq12d
    imbi12d
    rspccv
    syl
    syl5bir
    3imp
end
