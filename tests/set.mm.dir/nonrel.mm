include "ccnv.mm"
include "cdif.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cnvcnv.mm"
include "difeq2i.mm"
include "difin.mm"
include "eqtri.mm"

theorem nonrel
  let cA: class A


  assert |- ( A \ `' `' A ) = ( A \ ( _V X. _V ) )

  proof
    cA
    cA
    ccnv
    ccnv
    #
    cdif
    cA
    cA
    cvv
    cvv
    cxp
    #
    cin
    #
    cdif
    cA
    @1
    cdif
    @0
    @2
    cA
    cA
    cnvcnv
    difeq2i
    cA
    @1
    difin
    eqtri
end
