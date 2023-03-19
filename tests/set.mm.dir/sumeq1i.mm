include "wceq.mm"
include "csu.mm"
include "sumeq1.mm"
include "ax-mp.mm"

theorem sumeq1i
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume sumeq1i.1: |- A = B

  disjoint A k
  disjoint B k
  assert |- sum_ k e. A C = sum_ k e. B C

  proof
    cA
    cB
    wceq
    cA
    cC
    vk
    csu
    cB
    cC
    vk
    csu
    wceq
    sumeq1i.1
    cA
    cB
    cC
    vk
    sumeq1
    ax-mp
end
