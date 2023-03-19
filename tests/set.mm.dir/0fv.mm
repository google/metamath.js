include "c0.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "noel.mm"
include "dm0.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "ndmfv.mm"
include "ax-mp.mm"

theorem 0fv
  let cA: class A


  assert |- ( (/) ` A ) = (/)

  proof
    cA
    c0
    cdm
    #
    wcel
    #
    wn
    cA
    c0
    cfv
    c0
    wceq
    @1
    cA
    c0
    wcel
    cA
    noel
    @0
    c0
    cA
    dm0
    eleq2i
    mtbir
    cA
    c0
    ndmfv
    ax-mp
end
