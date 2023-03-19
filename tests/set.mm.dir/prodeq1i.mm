include "wceq.mm"
include "cprod.mm"
include "prodeq1.mm"
include "ax-mp.mm"

theorem prodeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq1i.1: |- A = B

  disjoint A k
  disjoint B k
  assert |- prod_ k e. A C = prod_ k e. B C

  proof
    cA
    cB
    wceq
    cA
    cC
    vk
    cprod
    cB
    cC
    vk
    cprod
    wceq
    prodeq1i.1
    cA
    cB
    cC
    vk
    prodeq1
    ax-mp
end
