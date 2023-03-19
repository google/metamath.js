include "wceq.mm"
include "cprod.mm"
include "prodeq2.mm"
include "mprg.mm"

theorem prodeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume prodeq2i.1: |- ( k e. A -> B = C )

  disjoint A k
  assert |- prod_ k e. A B = prod_ k e. A C

  proof
    cB
    cC
    wceq
    cA
    cB
    vk
    cprod
    cA
    cC
    vk
    cprod
    wceq
    vk
    cA
    cA
    cB
    cC
    vk
    prodeq2
    prodeq2i.1
    mprg
end
