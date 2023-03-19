include "cc0.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "negeq0.mm"
include "ax-mp.mm"
include "necon3bii.mm"

theorem negne0bi
  let cA: class A
  assume negidi.1: |- A e. CC


  assert |- ( A =/= 0 <-> -u A =/= 0 )

  proof
    cA
    cc0
    cA
    cneg
    #
    cc0
    cA
    cc
    wcel
    cA
    cc0
    wceq
    @0
    cc0
    wceq
    wb
    negidi.1
    cA
    negeq0
    ax-mp
    necon3bii
end
