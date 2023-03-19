include "wceq.mm"
include "crn.mm"
include "rneq.mm"
include "ax-mp.mm"

theorem rneqi
  let cA: class A
  let cB: class B
  assume rneqi.1: |- A = B


  assert |- ran A = ran B

  proof
    cA
    cB
    wceq
    cA
    crn
    cB
    crn
    wceq
    rneqi.1
    cA
    cB
    rneq
    ax-mp
end
