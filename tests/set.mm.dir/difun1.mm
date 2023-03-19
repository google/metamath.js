include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "cun.mm"
include "inass.mm"
include "invdif.mm"
include "eqtr3i.mm"
include "undm.mm"
include "ineq2i.mm"
include "difeq1i.mm"

theorem difun1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A \ ( B u. C ) ) = ( ( A \ B ) \ C )

  proof
    cA
    cvv
    cB
    cdif
    #
    cin
    #
    cC
    cdif
    #
    cA
    cB
    cC
    cun
    #
    cdif
    #
    cA
    cB
    cdif
    #
    cC
    cdif
    cA
    @0
    cvv
    cC
    cdif
    #
    cin
    #
    cin
    #
    @2
    @4
    @1
    @6
    cin
    @8
    @2
    cA
    @0
    @6
    inass
    @1
    cC
    invdif
    eqtr3i
    cA
    cvv
    @3
    cdif
    #
    cin
    @8
    @4
    @9
    @7
    cA
    cB
    cC
    undm
    ineq2i
    cA
    @3
    invdif
    eqtr3i
    eqtr3i
    @1
    @5
    cC
    cA
    cB
    invdif
    difeq1i
    eqtr3i
end
