include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "dfin2.mm"
include "ddif.mm"
include "difeq2i.mm"
include "eqtri.mm"

theorem invdif
  let cA: class A
  let cB: class B


  assert |- ( A i^i ( _V \ B ) ) = ( A \ B )

  proof
    cA
    cvv
    cB
    cdif
    #
    cin
    cA
    cvv
    @0
    cdif
    #
    cdif
    cA
    cB
    cdif
    cA
    @0
    dfin2
    @1
    cB
    cA
    cB
    ddif
    difeq2i
    eqtri
end
