include "chil.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "c0v.mm"
include "wceq.mm"
include "hvnegid.mm"
include "ax-mp.mm"

theorem hvnegidi
  let cA: class A
  assume hvaddid2.1: |- A e. ~H


  assert |- ( A +h ( -u 1 .h A ) ) = 0h

  proof
    cA
    chil
    wcel
    cA
    c1
    cneg
    cA
    csm
    co
    cva
    co
    c0v
    wceq
    hvaddid2.1
    cA
    hvnegid
    ax-mp
end
