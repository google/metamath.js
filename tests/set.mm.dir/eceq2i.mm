include "wceq.mm"
include "cec.mm"
include "eceq2.mm"
include "ax-mp.mm"

theorem eceq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume eceq2i.1: |- A = B


  assert |- [ C ] A = [ C ] B

  proof
    cA
    cB
    wceq
    cC
    cA
    cec
    cC
    cB
    cec
    wceq
    eceq2i.1
    cA
    cB
    cC
    eceq2
    ax-mp
end
