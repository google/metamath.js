include "wceq.mm"
include "ccnv.mm"
include "cnveq.mm"
include "ax-mp.mm"

theorem cnveqi
  let cA: class A
  let cB: class B
  assume cnveqi.1: |- A = B


  assert |- `' A = `' B

  proof
    cA
    cB
    wceq
    cA
    ccnv
    cB
    ccnv
    wceq
    cnveqi.1
    cA
    cB
    cnveq
    ax-mp
end
