include "cdif.mm"
include "wss.mm"
include "wrel.mm"
include "wi.mm"
include "difss.mm"
include "relss.mm"
include "ax-mp.mm"

theorem reldif
  let cA: class A
  let cB: class B


  assert |- ( Rel A -> Rel ( A \ B ) )

  proof
    cA
    cB
    cdif
    #
    cA
    wss
    cA
    wrel
    @0
    wrel
    wi
    cA
    cB
    difss
    @0
    cA
    relss
    ax-mp
end
