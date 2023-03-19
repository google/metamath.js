include "cun.mm"
include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "dfun2.mm"
include "dfin2.mm"
include "ddif.mm"
include "difeq2i.mm"
include "eqtr2i.mm"
include "eqtri.mm"

theorem dfun3
  let cA: class A
  let cB: class B


  assert |- ( A u. B ) = ( _V \ ( ( _V \ A ) i^i ( _V \ B ) ) )

  proof
    cA
    cB
    cun
    cvv
    cvv
    cA
    cdif
    #
    cB
    cdif
    #
    cdif
    cvv
    @0
    cvv
    cB
    cdif
    #
    cin
    #
    cdif
    cA
    cB
    dfun2
    @1
    @3
    cvv
    @3
    @0
    cvv
    @2
    cdif
    #
    cdif
    @1
    @0
    @2
    dfin2
    @4
    cB
    @0
    cB
    ddif
    difeq2i
    eqtr2i
    difeq2i
    eqtri
end
