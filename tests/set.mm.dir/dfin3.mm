include "cvv.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "ddif.mm"
include "dfun2.mm"
include "difeq1i.mm"
include "difeq2i.mm"
include "eqtri.mm"
include "dfin2.mm"
include "3eqtr4ri.mm"

theorem dfin3
  let cA: class A
  let cB: class B


  assert |- ( A i^i B ) = ( _V \ ( ( _V \ A ) u. ( _V \ B ) ) )

  proof
    cvv
    cvv
    cA
    cvv
    cB
    cdif
    #
    cdif
    #
    cdif
    #
    cdif
    @1
    cvv
    cvv
    cA
    cdif
    #
    @0
    cun
    #
    cdif
    cA
    cB
    cin
    @1
    ddif
    @4
    @2
    cvv
    @4
    cvv
    cvv
    @3
    cdif
    #
    @0
    cdif
    #
    cdif
    @2
    @3
    @0
    dfun2
    @6
    @1
    cvv
    @5
    cA
    @0
    cA
    ddif
    difeq1i
    difeq2i
    eqtri
    difeq2i
    cA
    cB
    dfin2
    3eqtr4ri
end
