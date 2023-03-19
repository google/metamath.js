include "wceq.mm"
include "cdm.mm"
include "dmeq.mm"
include "ax-mp.mm"

theorem dmeqi
  let cA: class A
  let cB: class B
  assume dmeqi.1: |- A = B


  assert |- dom A = dom B

  proof
    cA
    cB
    wceq
    cA
    cdm
    cB
    cdm
    wceq
    dmeqi.1
    cA
    cB
    dmeq
    ax-mp
end
