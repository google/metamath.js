include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "id.mm"
include "1cnd.mm"
include "pncand.mm"

theorem pncan1
  let cA: class A


  assert |- ( A e. CC -> ( ( A + 1 ) - 1 ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    @0
    id
    @0
    1cnd
    pncand
end
