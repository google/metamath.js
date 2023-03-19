include "wse.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-se.mm"
include "cab.mm"
include "dfrab3.mm"
include "wceq.mm"
include "vex.mm"
include "iniseg.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "eqtr4i.mm"
include "eleq1i.mm"
include "ralbii.mm"
include "bitri.mm"

theorem dfse2
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vy: setvar y

  disjoint A x
  disjoint R x
  disjoint x y
  disjoint A y
  disjoint R y
  assert |- ( R Se A <-> A. x e. A ( A i^i ( `' R " { x } ) ) e. _V )

  proof
    cA
    cR
    wse
    vy
    cv
    vx
    cv
    #
    cR
    wbr
    #
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    cA
    cR
    ccnv
    @0
    csn
    cima
    #
    cin
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    vx
    vy
    cA
    cR
    df-se
    @3
    @6
    vx
    cA
    @2
    @5
    cvv
    @2
    cA
    @1
    vy
    cab
    #
    cin
    @5
    @1
    vy
    cA
    dfrab3
    @4
    @7
    cA
    @0
    cvv
    wcel
    @4
    @7
    wceq
    vx
    vex
    vy
    cR
    @0
    cvv
    iniseg
    ax-mp
    ineq2i
    eqtr4i
    eleq1i
    ralbii
    bitri
end
