include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "cun.mm"
include "difindi.mm"
include "invdif.mm"
include "eqcomi.mm"
include "difeq2i.mm"
include "dfin2.mm"
include "uneq2i.mm"
include "3eqtr4i.mm"

theorem difdif2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A \ ( B \ C ) ) = ( ( A \ B ) u. ( A i^i C ) )

  proof
    cA
    cB
    cvv
    cC
    cdif
    #
    cin
    #
    cdif
    cA
    cB
    cdif
    #
    cA
    @0
    cdif
    #
    cun
    cA
    cB
    cC
    cdif
    #
    cdif
    @2
    cA
    cC
    cin
    #
    cun
    cA
    cB
    @0
    difindi
    @4
    @1
    cA
    @1
    @4
    cB
    cC
    invdif
    eqcomi
    difeq2i
    @5
    @3
    @2
    cA
    cC
    dfin2
    uneq2i
    3eqtr4i
end
