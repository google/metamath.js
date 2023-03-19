include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "hvaddid2.mm"
include "ax-mp.mm"

theorem hvaddid2i
  let cA: class A
  assume hvaddid2.1: |- A e. ~H


  assert |- ( 0h +h A ) = A

  proof
    cA
    chil
    wcel
    c0v
    cA
    cva
    co
    cA
    wceq
    hvaddid2.1
    cA
    hvaddid2
    ax-mp
end
