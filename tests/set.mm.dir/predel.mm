include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cpred.mm"
include "elinel1.mm"
include "df-pred.mm"
include "eleq2s.mm"

theorem predel
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y


  assert |- ( Y e. Pred ( R , A , X ) -> Y e. A )

  proof
    cY
    cA
    wcel
    cY
    cA
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    cA
    cR
    cX
    cpred
    cY
    cA
    @0
    elinel1
    cA
    cR
    cX
    df-pred
    eleq2s
end
