include "cvv.mm"
include "wceq.mm"
include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "vss.mm"
include "ssdif0.mm"
include "bitr3i.mm"

theorem vdif0
  let cA: class A


  assert |- ( A = _V <-> ( _V \ A ) = (/) )

  proof
    cA
    cvv
    wceq
    cvv
    cA
    wss
    cvv
    cA
    cdif
    c0
    wceq
    cA
    vss
    cvv
    cA
    ssdif0
    bitr3i
end
