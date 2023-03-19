include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "opidg.mm"
include "ax-mp.mm"

theorem opid
  let cA: class A
  assume opid.1: |- A e. _V


  assert |- <. A , A >. = { { A } }

  proof
    cA
    cvv
    wcel
    cA
    cA
    cop
    cA
    csn
    csn
    wceq
    opid.1
    cA
    cvv
    opidg
    ax-mp
end
