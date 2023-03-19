include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "rdgsucg.mm"
include "df-r1.mm"
include "dmeqi.mm"
include "eleq2s.mm"
include "fveq1i.mm"
include "fvex.mm"
include "pweq.mm"
include "eqid.mm"
include "pwex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"

theorem r1sucg
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. dom R1 -> ( R1 ` suc A ) = ~P ( R1 ` A ) )

  proof
    cA
    cr1
    cdm
    #
    wcel
    cA
    csuc
    #
    vx
    cvv
    vx
    cv
    #
    cpw
    #
    cmpt
    #
    c0
    crdg
    #
    cfv
    #
    cA
    @5
    cfv
    #
    @4
    cfv
    #
    @1
    cr1
    cfv
    cA
    cr1
    cfv
    #
    cpw
    #
    @6
    @8
    wceq
    cA
    @5
    cdm
    @0
    c0
    cA
    @4
    rdgsucg
    cr1
    @5
    vx
    df-r1
    #
    dmeqi
    eleq2s
    @1
    cr1
    @5
    @11
    fveq1i
    @9
    @4
    cfv
    #
    @10
    @8
    @9
    cvv
    wcel
    @12
    @10
    wceq
    cA
    cr1
    fvex
    #
    vx
    @9
    @3
    @10
    cvv
    @4
    @2
    @9
    pweq
    @4
    eqid
    @9
    @13
    pwex
    fvmpt
    ax-mp
    @9
    @7
    @4
    cA
    cr1
    @5
    @11
    fveq1i
    fveq2i
    eqtr3i
    3eqtr4g
end
