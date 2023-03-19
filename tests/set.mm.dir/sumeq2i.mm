include "wceq.mm"
include "csu.mm"
include "sumeq2.mm"
include "mprg.mm"

theorem sumeq2i
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq2i.1: |- ( k e. A -> B = C )

  disjoint A k
  assert |- sum_ k e. A B = sum_ k e. A C

  proof
    cB
    cC
    wceq
    cA
    cB
    vk
    csu
    cA
    cC
    vk
    csu
    wceq
    vk
    cA
    cA
    cB
    cC
    vk
    sumeq2
    sumeq2i.1
    mprg
end
