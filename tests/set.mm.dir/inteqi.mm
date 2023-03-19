include "wceq.mm"
include "cint.mm"
include "inteq.mm"
include "ax-mp.mm"

theorem inteqi
  let cA: class A
  let cB: class B
  assume inteqi.1: |- A = B


  assert |- |^| A = |^| B

  proof
    cA
    cB
    wceq
    cA
    cint
    cB
    cint
    wceq
    inteqi.1
    cA
    cB
    inteq
    ax-mp
end
