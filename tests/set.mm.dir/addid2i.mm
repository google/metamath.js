include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addid2.mm"
include "ax-mp.mm"

theorem addid2i
  let cA: class A
  assume mul.1: |- A e. CC


  assert |- ( 0 + A ) = A

  proof
    cA
    cc
    wcel
    cc0
    cA
    caddc
    co
    cA
    wceq
    mul.1
    cA
    addid2
    ax-mp
end
