include "cun.mm"
include "cdif.mm"
include "cvv.mm"
include "cin.mm"
include "dfun3.mm"
include "difeq2i.mm"
include "inindi.mm"
include "dfin2.mm"
include "invdif.mm"
include "ineq12i.mm"
include "3eqtr3i.mm"
include "eqtri.mm"

theorem difundi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A \ ( B u. C ) ) = ( ( A \ B ) i^i ( A \ C ) )

  proof
    cA
    cB
    cC
    cun
    #
    cdif
    cA
    cvv
    cvv
    cB
    cdif
    #
    cvv
    cC
    cdif
    #
    cin
    #
    cdif
    #
    cdif
    #
    cA
    cB
    cdif
    #
    cA
    cC
    cdif
    #
    cin
    #
    @0
    @4
    cA
    cB
    cC
    dfun3
    difeq2i
    cA
    @3
    cin
    cA
    @1
    cin
    #
    cA
    @2
    cin
    #
    cin
    @5
    @8
    cA
    @1
    @2
    inindi
    cA
    @3
    dfin2
    @9
    @6
    @10
    @7
    cA
    cB
    invdif
    cA
    cC
    invdif
    ineq12i
    3eqtr3i
    eqtri
end
