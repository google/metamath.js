include "csu.mm"
include "sumeq2i.mm"
include "sumeq1i.mm"
include "eqtri.mm"

theorem sumeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume sumeq12i.1: |- A = B
  assume sumeq12i.2: |- ( k e. A -> C = D )

  disjoint A k
  disjoint B k
  assert |- sum_ k e. A C = sum_ k e. B D

  proof
    cA
    cC
    vk
    csu
    cA
    cD
    vk
    csu
    cB
    cD
    vk
    csu
    cA
    cC
    cD
    vk
    sumeq12i.2
    sumeq2i
    cA
    cB
    cD
    vk
    sumeq12i.1
    sumeq1i
    eqtri
end
