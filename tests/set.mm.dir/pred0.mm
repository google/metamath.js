include "c0.mm"
include "cpred.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "df-pred.mm"
include "0in.mm"
include "eqtri.mm"

theorem pred0
  let cR: class R
  let cX: class X


  assert |- Pred ( R , (/) , X ) = (/)

  proof
    c0
    cR
    cX
    cpred
    c0
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    c0
    c0
    cR
    cX
    df-pred
    @0
    0in
    eqtri
end
