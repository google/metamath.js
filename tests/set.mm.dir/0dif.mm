include "c0.mm"
include "cdif.mm"
include "wss.mm"
include "wceq.mm"
include "difss.mm"
include "ss0.mm"
include "ax-mp.mm"

theorem 0dif
  let cA: class A


  assert |- ( (/) \ A ) = (/)

  proof
    c0
    cA
    cdif
    #
    c0
    wss
    @0
    c0
    wceq
    c0
    cA
    difss
    @0
    ss0
    ax-mp
end
