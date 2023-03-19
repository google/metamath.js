include "cin.mm"
include "cvv.mm"
include "cdif.mm"
include "inass.mm"
include "invdif.mm"
include "ineq2i.mm"
include "3eqtr3ri.mm"

theorem indif2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B \ C ) ) = ( ( A i^i B ) \ C )

  proof
    cA
    cB
    cin
    #
    cvv
    cC
    cdif
    #
    cin
    cA
    cB
    @1
    cin
    #
    cin
    @0
    cC
    cdif
    cA
    cB
    cC
    cdif
    #
    cin
    cA
    cB
    @1
    inass
    @0
    cC
    invdif
    @2
    @3
    cA
    cB
    cC
    invdif
    ineq2i
    3eqtr3ri
end
