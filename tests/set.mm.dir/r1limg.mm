include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "cima.mm"
include "cuni.mm"
include "ciun.mm"
include "wceq.mm"
include "df-r1.mm"
include "dmeqi.mm"
include "eleq2i.mm"
include "rdglimg.mm"
include "sylanb.mm"
include "fveq1i.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpli.mm"
include "funiunfv.mm"
include "ax-mp.mm"
include "imaeq1i.mm"
include "unieqi.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem r1limg
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( A e. dom R1 /\ Lim A ) -> ( R1 ` A ) = U_ x e. A ( R1 ` x ) )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    wlim
    #
    wa
    cA
    vy
    cvv
    vy
    cv
    cpw
    cmpt
    #
    c0
    crdg
    #
    cfv
    #
    @4
    cA
    cima
    #
    cuni
    #
    cA
    cr1
    cfv
    vx
    cA
    vx
    cv
    cr1
    cfv
    ciun
    #
    @1
    cA
    @4
    cdm
    #
    wcel
    @2
    @5
    @7
    wceq
    @0
    @9
    cA
    cr1
    @4
    vy
    df-r1
    #
    dmeqi
    eleq2i
    c0
    cA
    @3
    rdglimg
    sylanb
    cA
    cr1
    @4
    @10
    fveq1i
    @8
    cr1
    cA
    cima
    #
    cuni
    #
    @7
    cr1
    wfun
    #
    @8
    @12
    wceq
    @13
    @0
    wlim
    r1funlim
    simpli
    vx
    cA
    cr1
    funiunfv
    ax-mp
    @11
    @6
    cr1
    @4
    cA
    @10
    imaeq1i
    unieqi
    eqtri
    3eqtr4g
end
