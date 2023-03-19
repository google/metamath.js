include "cin.mm"
include "cdif.mm"
include "cvv.mm"
include "cun.mm"
include "dfin3.mm"
include "difeq2i.mm"
include "indi.mm"
include "dfin2.mm"
include "invdif.mm"
include "uneq12i.mm"
include "3eqtr3i.mm"
include "eqtri.mm"

theorem difindi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A \ ( B i^i C ) ) = ( ( A \ B ) u. ( A \ C ) )

  proof
    cA
    cB
    cC
    cin
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
    cun
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
    cun
    #
    @0
    @4
    cA
    cB
    cC
    dfin3
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
    cun
    @5
    @8
    cA
    @1
    @2
    indi
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
    uneq12i
    3eqtr3i
    eqtri
end
