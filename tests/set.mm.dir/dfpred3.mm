include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "cin.mm"
include "cpred.mm"
include "crab.mm"
include "incom.mm"
include "dfpred2.mm"
include "dfrab2.mm"
include "3eqtr4i.mm"

theorem dfpred3
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  assume dfpred2.1: |- X e. _V

  disjoint R y
  disjoint X y
  disjoint A y
  assert |- Pred ( R , A , X ) = { y e. A | y R X }

  proof
    cA
    vy
    cv
    cX
    cR
    wbr
    #
    vy
    cab
    #
    cin
    @1
    cA
    cin
    cA
    cR
    cX
    cpred
    @0
    vy
    cA
    crab
    cA
    @1
    incom
    vy
    cA
    cR
    cX
    dfpred2.1
    dfpred2
    @0
    vy
    cA
    dfrab2
    3eqtr4i
end
