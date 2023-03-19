include "cun.mm"
include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "indir.mm"
include "invdif.mm"
include "uneq12i.mm"
include "3eqtr3i.mm"

theorem difundir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) \ C ) = ( ( A \ C ) u. ( B \ C ) )

  proof
    cA
    cB
    cun
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
    cun
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
    cun
    cA
    cB
    @1
    indir
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
    uneq12i
    3eqtr3i
end
