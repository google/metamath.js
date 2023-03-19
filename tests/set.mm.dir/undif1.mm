include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "cun.mm"
include "undir.mm"
include "invdif.mm"
include "uneq1i.mm"
include "uncom.mm"
include "unvdif.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "inv1.mm"
include "3eqtr3i.mm"

theorem undif1
  let cA: class A
  let cB: class B


  assert |- ( ( A \ B ) u. B ) = ( A u. B )

  proof
    cA
    cvv
    cB
    cdif
    #
    cin
    #
    cB
    cun
    cA
    cB
    cun
    #
    @0
    cB
    cun
    #
    cin
    #
    cA
    cB
    cdif
    #
    cB
    cun
    @2
    cA
    @0
    cB
    undir
    @1
    @5
    cB
    cA
    cB
    invdif
    uneq1i
    @4
    @2
    cvv
    cin
    @2
    @3
    cvv
    @2
    @3
    cB
    @0
    cun
    cvv
    @0
    cB
    uncom
    cB
    unvdif
    eqtri
    ineq2i
    @2
    inv1
    eqtri
    3eqtr3i
end
