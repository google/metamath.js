include "cdif.mm"
include "cun.mm"
include "uncom.mm"
include "undif1.mm"
include "3eqtri.mm"

theorem undif2
  let cA: class A
  let cB: class B


  assert |- ( A u. ( B \ A ) ) = ( A u. B )

  proof
    cA
    cB
    cA
    cdif
    #
    cun
    @0
    cA
    cun
    cB
    cA
    cun
    cA
    cB
    cun
    cA
    @0
    uncom
    cB
    cA
    undif1
    cB
    cA
    uncom
    3eqtri
end
