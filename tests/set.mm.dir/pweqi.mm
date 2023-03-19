include "wceq.mm"
include "cpw.mm"
include "pweq.mm"
include "ax-mp.mm"

theorem pweqi
  let cA: class A
  let cB: class B
  assume pweqi.1: |- A = B


  assert |- ~P A = ~P B

  proof
    cA
    cB
    wceq
    cA
    cpw
    cB
    cpw
    wceq
    pweqi.1
    cA
    cB
    pweq
    ax-mp
end
