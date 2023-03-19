include "cdif.mm"
include "cvv.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "dif32.mm"
include "invdif.mm"
include "eqtr4i.mm"
include "un0.mm"
include "indi.mm"
include "disjdif.mm"
include "incom.mm"
include "eqtr3i.mm"
include "uneq2i.mm"
include "ddif.mm"
include "indm.mm"
include "difeq2i.mm"
include "ineq2i.mm"
include "3eqtri.mm"

theorem difdifdir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ ( B \ C ) )

  proof
    cA
    cB
    cdif
    cC
    cdif
    #
    cA
    cC
    cdif
    #
    cvv
    cB
    cdif
    #
    cC
    cun
    #
    cin
    #
    @1
    cvv
    cB
    cC
    cdif
    #
    cdif
    #
    cin
    @1
    @5
    cdif
    @0
    @1
    @2
    cin
    #
    c0
    cun
    #
    @4
    @0
    @7
    @8
    @0
    @1
    cB
    cdif
    @7
    cA
    cB
    cC
    dif32
    @1
    cB
    invdif
    eqtr4i
    @7
    un0
    eqtr4i
    @4
    @7
    @1
    cC
    cin
    #
    cun
    @8
    @1
    @2
    cC
    indi
    c0
    @9
    @7
    cC
    @1
    cin
    c0
    @9
    cC
    cA
    disjdif
    cC
    @1
    incom
    eqtr3i
    uneq2i
    eqtr4i
    eqtr4i
    @3
    @6
    @1
    @2
    cvv
    cvv
    cC
    cdif
    #
    cdif
    #
    cun
    #
    @3
    @6
    @11
    cC
    @2
    cC
    ddif
    uneq2i
    cvv
    cB
    @10
    cin
    #
    cdif
    @12
    @6
    cB
    @10
    indm
    @13
    @5
    cvv
    cB
    cC
    invdif
    difeq2i
    eqtr3i
    eqtr3i
    ineq2i
    @1
    @5
    invdif
    3eqtri
end
