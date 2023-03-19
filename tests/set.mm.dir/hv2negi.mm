include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cmv.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wceq.mm"
include "hv2neg.mm"
include "ax-mp.mm"

theorem hv2negi
  let cA: class A
  assume hvaddid2.1: |- A e. ~H


  assert |- ( 0h -h A ) = ( -u 1 .h A )

  proof
    cA
    chil
    wcel
    c0v
    cA
    cmv
    co
    c1
    cneg
    cA
    csm
    co
    wceq
    hvaddid2.1
    cA
    hv2neg
    ax-mp
end
