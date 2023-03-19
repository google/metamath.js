include "cdif.mm"
include "wss.mm"
include "id.mm"
include "difss.mm"
include "syl6ss.mm"

theorem difss2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ ( B \ C ) -> A C_ B )

  proof
    cA
    cB
    cC
    cdif
    #
    wss
    #
    cA
    @0
    cB
    @1
    id
    cB
    cC
    difss
    syl6ss
end
