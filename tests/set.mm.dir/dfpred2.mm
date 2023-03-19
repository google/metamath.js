include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "df-pred.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "iniseg.mm"
include "ax-mp.mm"
include "ineq2i.mm"
include "eqtri.mm"

theorem dfpred2
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  assume dfpred2.1: |- X e. _V

  disjoint R y
  disjoint X y
  assert |- Pred ( R , A , X ) = ( A i^i { y | y R X } )

  proof
    cA
    cR
    cX
    cpred
    cA
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    cA
    vy
    cv
    cX
    cR
    wbr
    vy
    cab
    #
    cin
    cA
    cR
    cX
    df-pred
    @0
    @1
    cA
    cX
    cvv
    wcel
    @0
    @1
    wceq
    dfpred2.1
    vy
    cR
    cX
    cvv
    iniseg
    ax-mp
    ineq2i
    eqtri
end
