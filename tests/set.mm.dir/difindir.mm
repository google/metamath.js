include "cin.mm"
include "cvv.mm"
include "cdif.mm"
include "inindir.mm"
include "invdif.mm"
include "ineq12i.mm"
include "3eqtr3i.mm"

theorem difindir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) \ C ) = ( ( A \ C ) i^i ( B \ C ) )

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
    @1
    cin
    #
    cB
    @1
    cin
    #
    cin
    @0
    cC
    cdif
    cA
    cC
    cdif
    #
    cB
    cC
    cdif
    #
    cin
    cA
    cB
    @1
    inindir
    @0
    cC
    invdif
    @2
    @4
    @3
    @5
    cA
    cC
    invdif
    cB
    cC
    invdif
    ineq12i
    3eqtr3i
end
